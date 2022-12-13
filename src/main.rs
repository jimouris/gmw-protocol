use bitvec::prelude::*;

struct Party {
    id: usize,
    x: BitVec<u8>,
    y: BitVec<u8>,
}

struct Dealer {
    k: Vec<u8>,
    c: u8,
    kc: u8,
}

impl Dealer {
    pub fn new() -> Dealer {
        let k = vec![rand::random::<u8>() % 2,rand::random::<u8>() % 2];
        let c = rand::random::<u8>() % 2;
        Dealer { kc: k[c as usize], k: k, c: c, }
    }
}

fn secret_share(bit_array: &BitVec<u8>) -> (BitVec<u8>, BitVec<u8>) {
    let mut sh_1 = BitVec::<u8>::with_capacity(bit_array.len());
    let mut sh_2 = BitVec::<u8>::with_capacity(bit_array.len());
    for i in 0..bit_array.len() {
        sh_1.push(rand::random::<bool>());
        sh_2.push(sh_1[i] ^ bit_array[i]);
    }
    (sh_1, sh_2)
}

fn reconstruct_shares(ss0: &BitVec<u8>, ss1: &BitVec<u8>) -> BitVec<u8> {
    assert_eq!(ss0.len(), ss1.len());
    let mut reconstructed = BitVec::<u8>::with_capacity(ss0.len());
    for (b0, b1) in ss0.iter().zip(ss1.iter()) {
        reconstructed.push(*b0 ^ *b1);
    }
    reconstructed
}

// NOT: ~x
fn not_gate(id: usize, ss: &BitVec<u8>) -> BitVec<u8> {
    if id == 0 {
        let mut not_ss = BitVec::<u8>::with_capacity(ss.len());
        for b in ss {
            not_ss.push(!b);
        }
        not_ss
    } else {
        ss.clone()
    }
}

// XOR: z = x xor y
fn xor_gate(x_ss: &BitVec<u8>, y_ss: &BitVec<u8>) -> BitVec<u8> {
    let mut xor_ss = BitVec::<u8>::with_capacity(x_ss.len());
    for (xi, yi) in x_ss.iter().zip(y_ss.iter()) {
        xor_ss.push(*xi ^ *yi);
    }
    xor_ss
}

// P0 is the Sender with inputs (m0, m1)
// P1 is the Receiver with inputs (b, mb)
fn one_out_of_two_ot(
    dealer: &Dealer,
    receiver_b: u8,
    sender_m: &Vec<u8>) -> u8
{
    let z = receiver_b ^ dealer.c;
    let y = {
        if z == 0 {
            vec![sender_m[0] ^ dealer.k[0], sender_m[1] ^ dealer.k[1]]
        } else {
            vec![sender_m[0] ^ dealer.k[1], sender_m[1] ^ dealer.k[0]]
        }
    };

    y[receiver_b as usize] ^ dealer.kc
}

// AND: z = x & y
//  x & y = x * y = (p0.x + p1.x) * (p0.y + p1.y) =
//  (p0.x * p0.y) + (p0.x * p1.y) + (p0.y * p1.x) + (p1.x * p1.y)
//  P0 computes locally p0.x * p0.y
//  P1 computes locally p1.x * p1.y
//  Both parties compute via OT: p0.x * p1.y and p1.x * p0.y
fn and_gate(p0: &Party, p1: &Party) -> (BitVec<u8>, BitVec<u8>) {
    // Online Phase - P1 receives r0 + p0.x * p1.y
    let mut r0 = BitVec::<u8>::with_capacity(p0.x.len());
    let mut r0_x0y1 = BitVec::<u8>::with_capacity(p0.x.len());
    for i in 0..p0.x.len() {
        let dealer = Dealer::new();
        r0.push(rand::random::<bool>());
        r0_x0y1.push(
            one_out_of_two_ot(
                &dealer,
                p1.y[i] as u8,
                &vec![r0[i] as u8, (p0.x[i] as u8) ^ (r0[i] as u8)]
            ) != 0
        );
    }

    // Online Phase - P0 receives r1 + p1.x * p0.y
    let mut r1 = BitVec::<u8>::with_capacity(p1.x.len());
    let mut r1_x1y0 = BitVec::<u8>::with_capacity(p1.x.len());
    for i in 0..p1.x.len() {
        let dealer = Dealer::new();
        // r0.push(rand::random::<u8>() % 2);
        r1.push(rand::random::<bool>());
        r1_x1y0.push(
            one_out_of_two_ot(
                &dealer,
                p0.y[i] as u8,
                &vec![r1[i] as u8, (p1.x[i] as u8) ^ (r1[i] as u8)]
            ) != 0
        );
    }

    // P0
    let mut share_0 = BitVec::<u8>::with_capacity(p0.x.len());
    for i in 0..p0.x.len() {
        share_0.push(
            (p0.x[i] & p0.y[i]) ^ (r0[i] ^ r1_x1y0[i])
        );
    }

    // P1
    let mut share_1 = BitVec::<u8>::with_capacity(p1.x.len());
    for i in 0..p1.x.len() {
        share_1.push(
            (p1.x[i] & p1.y[i]) ^ (r1[i] ^ r0_x0y1[i])
        );
    }

    (share_0, share_1)
}

// OR: z = x | y = ~(~x & ~y)
//   ~(~x & ~y) = ~(~x * ~y) = ~( ~(p0.x + p1.x) * ~(p0.y + p1.y) ) =
//  ~( (~p0.x + p1.x) * (~p0.y + p1.y) ) =
//  ~( (~p0.x * ~p0.y) + (~p0.x * p1.y) + (p1.x * ~p0.y) + (p1.x * p1.y) ) =
//  P0 computes locally ~p0.x * ~p0.y
//  P1 computes locally p1.x * p1.y
//  Both parties compute via OT: ~p0.x * p1.y and p1.x * ~p0.y
fn or_gate(p0: &Party, p1: &Party) -> (BitVec<u8>, BitVec<u8>) {
    // Online Phase - P1 receives r0 + p0.x * p1.y
    let mut r0 = BitVec::<u8>::with_capacity(p0.x.len());
    let mut r0_x0y1 = BitVec::<u8>::with_capacity(p0.x.len());
    for i in 0..p0.x.len() {
        let dealer = Dealer::new();
        r0.push(rand::random::<bool>());

    // let r0_notx0y1 = one_out_of_two_ot(&k, c, kc, y_1, &vec![r0, (1 - x_0) ^ r0]);

        r0_x0y1.push(
            one_out_of_two_ot(
                &dealer,
                p1.y[i] as u8,
                &vec![r0[i] as u8, (!p0.x[i] as u8) ^ (r0[i] as u8)]
            ) != 0
        );
    }

    // Online Phase - P0 receives r1 + p1.x * p0.y
    let mut r1 = BitVec::<u8>::with_capacity(p1.x.len());
    let mut r1_x1y0 = BitVec::<u8>::with_capacity(p1.x.len());
    for i in 0..p1.x.len() {
        let dealer = Dealer::new();
        // r0.push(rand::random::<u8>() % 2);
        r1.push(rand::random::<bool>());
        r1_x1y0.push(
            one_out_of_two_ot(
                &dealer,
                !p0.y[i] as u8,
                &vec![r1[i] as u8, (p1.x[i] as u8) ^ (r1[i] as u8)]
            ) != 0
        );
    }

    // P0
    let mut share_0 = BitVec::<u8>::with_capacity(p0.x.len());
    for i in 0..p0.x.len() {
        share_0.push(
            !((!p0.x[i] & !p0.y[i]) ^ (r0[i] ^ r1_x1y0[i]))
        );
    }

    // P1
    let mut share_1 = BitVec::<u8>::with_capacity(p1.x.len());
    for i in 0..p1.x.len() {
        share_1.push(
            (p1.x[i] & p1.y[i]) ^ (r1[i] ^ r0_x0y1[i])
        );
    }

    (share_0, share_1)
}

fn main() {
    let x = bitvec![u8, Lsb0; 0, 0, 1, 1];
    let y = bitvec![u8, Lsb0; 0, 1, 0, 1];
    let mut z = bitvec![u8, Lsb0; 0; 4];

    // Shares of x and y
    let (x0, x1) = secret_share(&x);
    let (y0, y1) = secret_share(&y);
    let p0 = Party { id: 0, x: x0, y: y0 };
    let p1 = Party { id: 1, x: x1, y: y1 };

    println!("x\t:\t{} = {} ^ {}", x, p0.x, p1.x);
    println!("y\t:\t{} = {} ^ {}", y, p0.y, p1.y);

    // NOT gate
    let not_x0 = not_gate(p0.id, &p0.x);
    let not_x1 = not_gate(p1.id, &p1.x);
    let not_x_mpc = reconstruct_shares(&not_x0, &not_x1);
    for i in 0..x.len() {
        z.set(i, !x[i]);
        assert_eq!(z[i], not_x_mpc[i]);
    }
    println!("~x\t:\t{} = {} ^ {}", z, not_x0, not_x1);

    // XOR gate
    let x0_xor_y0 = xor_gate(&p0.x, &p0.y);
    let x1_xor_y1 = xor_gate(&p1.x, &p1.y);
    let x_xor_y_mpc = reconstruct_shares(&x0_xor_y0, &x1_xor_y1);
    for i in 0..x.len() {
        z.set(i, x[i] ^ y[i]);
        assert_eq!(z[i], x_xor_y_mpc[i]);
    }
    println!("x ^ y\t:\t{} = {} ^ {}", z, x0_xor_y0, x1_xor_y1);

    // OT:
    //  P0 is the Sender with inputs (m0, m1).
    //  P1 is the Receiver with inputs (b, mb).
    //  A third party runs the dealer.
    let sender = vec![10, 20];
    for bit in 0..2 {
        let dealer = Dealer::new();
        let mb = one_out_of_two_ot(&dealer, bit, &sender);
        println!("OT:\n  receiver b: {}\n  sender [m0, m1]: {:?}\n  mb: {}", bit, sender, mb);
    }

    // AND gate
    let (x0_and_y0, x1_and_y1) = and_gate(&p0, &p1);
    let x_and_y_mpc = reconstruct_shares(&x0_and_y0, &x1_and_y1);
    for i in 0..x.len() {
        z.set(i, x[i] & y[i]);
        assert_eq!(z[i], x_and_y_mpc[i]);
    }
    println!("x & y\t:\t{} = {} ^ {}", z, x0_and_y0, x1_and_y1);


    // OR gate
    let (x0_or_y0, x1_or_y1) = or_gate(&p0, &p1);
    let x_or_y_mpc = reconstruct_shares(&x0_or_y0, &x1_or_y1);
    for i in 0..x.len() {
        z.set(i, x[i] | y[i]);
        assert_eq!(z[i], x_or_y_mpc[i]);
    }
    println!("x | y\t:\t{} = {} ^ {}", z, x0_or_y0, x1_or_y1);

}
