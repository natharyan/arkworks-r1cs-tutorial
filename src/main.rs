use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystemRef, SynthesisError,
};
use ark_relations::r1cs::{ConstraintSystem, ConstraintMatrices, SynthesisMode};
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, eq::EqGadget};
use ark_ff::{PrimeField};
use ark_bls12_381::Fr;
use std::env;
use ark_groth16::{Groth16, ProvingKey, VerifyingKey, Proof};
use ark_snark::SNARK;
use ark_bls12_381::Bls12_381;
use ark_std::rand::thread_rng;
use std::time::Instant;

#[derive(Clone, Debug)]
pub struct CubeCircuit<F: PrimeField> {
    pub x: F, // private input (witness)
    pub y: F, // public input (x^3 + x + 5)
}

impl<F: PrimeField> ConstraintSynthesizer<F> for CubeCircuit<F> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(), SynthesisError> {
        let y_var: FpVar<F> = FpVar::new_input(cs.clone(), || Ok(self.y))?;
        let x_var: FpVar<F> = FpVar::new_witness(cs.clone(), || Ok(self.x))?;

        // constrain x^2 = x * x
        let x_squared_var = x_var.clone() * x_var.clone();
        // constrain x^3 = x^2 * x
        let x_cubed_var = x_squared_var * x_var.clone();
        // constrain y = x^3 + x + 5
        (&x_var + &FpVar::Constant(F::from(5u64)) + x_cubed_var).enforce_equal(&y_var)?;
        Ok(())
    }
}

fn main() {
    unsafe { env::set_var("RUST_BACKTRACE", "1"); }
    let x_value = Fr::from(3u64);
    // y = x^3 + x + 5
    // 3^3 + 3 + 5 = 9*3 + 3 + 5 = 35
    let y_value = x_value * x_value * x_value + x_value + Fr::from(5u64);

    let circuit = CubeCircuit {
        x: x_value,
        y: y_value,
    };

    let cs = ConstraintSystem::new_ref();
    circuit.clone().generate_constraints(cs.clone()).unwrap();
    assert!(cs.is_satisfied().unwrap());
    println!("Equation: y = x^3 + x + 5");
    println!("Private input x: {}", x_value);
    println!("Public input y: {}", y_value);
    println!("Constraint system is satisfied: {}", cs.is_satisfied().unwrap());
    println!("Number of constraints: {}", cs.num_constraints());
    println!("Field size: {}", Fr::MODULUS);

    let mut z = vec![];
    z.extend(cs.borrow().unwrap().instance_assignment.clone());
    z.extend(cs.borrow().unwrap().witness_assignment.clone());

    // get the integer values of z from BigInt representation

    let z_str = z.iter().map(|val| val.to_string()).collect::<Vec<String>>();
    println!("\nVector z: [{}]", z_str.join(", "));

    let (instance, witness) = z.split_at(cs.borrow().unwrap().instance_assignment.len());
    let instance_str = instance.iter().map(|val| val.to_string()).collect::<Vec<String>>();
    let witness_str = witness.iter().map(|val| val.to_string()).collect::<Vec<String>>();
    println!("\nInstance variables: [{}]", instance_str.join(", "));
    println!("Witness variables: [{}]", witness_str.join(", "));

    cs.inline_all_lcs();
    let matrices: ConstraintMatrices<Fr> = cs.borrow().unwrap().to_matrices().unwrap();
    // rows are (value in the matrix, col_index(equal to z index))
    let a: Vec<Vec<(Fr, usize)>> = matrices.a;
    let b: Vec<Vec<(Fr, usize)>> = matrices.b;
    let c: Vec<Vec<(Fr, usize)>> = matrices.c;
    
    // convert to BigInt to string. BigInt: x = a0​+  (a_1​ × 2^64) + (a_2 ​× 2^128) + (a_3 ​× 2^192)
    let a_str: Vec<Vec<(String, usize)>> = a.iter().map(|row| row.iter().map(|(val, idx)| (val.to_string(), *idx)).collect()).collect();
    let b_str: Vec<Vec<(String, usize)>> = b.iter().map(|row| row.iter().map(|(val, idx)| (val.to_string(), *idx)).collect()).collect();
    let c_str: Vec<Vec<(String, usize)>> = c.iter().map(|row| row.iter().map(|(val, idx)| (val.to_string(), *idx)).collect()).collect();


    println!("\nMatrix A:");
    for row in a_str.iter() {
        println!("[{}]", row.iter().map(|(val, idx)| format!("({}, {})", val, idx)).collect::<Vec<_>>().join(", "));
    }
    println!("\nMatrix B:");
    for row in b_str.iter() {
        println!("[{}]", row.iter().map(|(val, idx)| format!("({}, {})", val, idx)).collect::<Vec<_>>().join(", "));
    }
    println!("\nMatrix C:");
    for row in c_str.iter() {
        println!("[{}]", row.iter().map(|(val, idx)| format!("({}, {})", val, idx)).collect::<Vec<_>>().join(", "));
    }

    // z = [1, 35, 3, 9, 27] = [1] + [public input] + [private witnesses]
    // each constraint adds a row to the matrices
    // enforces x^2 = x * x
    // A: [(1, 2)] => 1*z[2] = 1*3 = 3
    // B: [(1, 2)] => 1*z[2] = 1*3 = 3
    // C: [(1, 3)] => 1*z[3] = 1*9 = 9

    // enforces x^3 = x^2 * x
    // A: [(1, 3)] => 1*z[3] = 1*9 = 9
    // B: [(1, 2)] => 1*z[2] = 1*3 = 3
    // C: [(1, 4)] => 1*z[4] = 1*27 = 27

    // enforces x^3 + x + 5 - y = 0
    // A: [(5, 0), (-1, 1), (1, 2), (1, 4)] => 5*1 + (-1)*35 + 1*3 + 1*27 = 5 - 35 + 3 + 27 = 0
    // B: [(1, 0)] => 1*z[0] = 1*1 = 1
    // C: [] => 0

    // setup
    let mut rng = thread_rng();
    let (pk, vk): (ProvingKey<Bls12_381>, VerifyingKey<Bls12_381>) = 
        Groth16::<Bls12_381>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();

    // prove
    let prove_start = Instant::now();
    let proof: Proof<Bls12_381> = Groth16::<Bls12_381>::prove(&pk, circuit.clone(), &mut rng).unwrap();
    let prove_time = prove_start.elapsed();
    println!("\nProof generated successfully in {:?}", prove_time);

    // verify
    let verify_start = Instant::now();
    let valid = Groth16::<Bls12_381>::verify(&vk, &[y_value], &proof).unwrap();
    let verify_time = verify_start.elapsed();
    println!("Proof verification result: {} in {:?}", valid, verify_time);

}