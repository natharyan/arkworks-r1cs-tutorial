use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystemRef, SynthesisError,
};
use ark_relations::r1cs::{ConstraintSystem, ConstraintMatrices, SynthesisMode};
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, eq::EqGadget};
use ark_ff::{PrimeField};
use ark_bls12_381::Fr;
use std::env;

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
    // 3^3 + 3 + 5 = 9*3 + 3 + 5 = 35
    let y_value = x_value * x_value * x_value + x_value + Fr::from(5u64);

    let circuit = CubeCircuit {
        x: x_value,
        y: y_value,
    };

    let cs = ConstraintSystem::new_ref();
    // cs.set_mode(SynthesisMode::Setup); // stores symbolic representations of constraints to enable use of to_matrices()
    circuit.generate_constraints(cs.clone()).unwrap();
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

    println!("\nVector z: {:?}", z);

    let (instance, witness) = z.split_at(cs.borrow().unwrap().instance_assignment.len());
    println!("Instance variables: {:?}", instance);
    println!("Witness variables: {:?}", witness);

    cs.inline_all_lcs();
    let matrices: ConstraintMatrices<Fr> = cs.borrow().unwrap().to_matrices().unwrap();
    // rows are (value in the matrix, col_index(equal to z index))
    let a: Vec<Vec<(Fr, usize)>> = matrices.a;
    let b: Vec<Vec<(Fr, usize)>> = matrices.b;
    let c: Vec<Vec<(Fr, usize)>> = matrices.c;

    println!("\nMatrix A:");
    for row in a.iter() {
        println!("{:?}", row); 
    } // 52435875175126190479447740508185965837690552500527637822603658699938581184512 \equiv -1 mod p
    println!("\nMatrix B:");
    for row in b.iter() {
        println!("{:?}", row);
    }

    println!("\nMatrix C:");
    for row in c.iter() {
        println!("{:?}", row);
    }

    // Enforces x^2 = x * x
    // A: [(1, 2)] => 1*z[2] = 1*3 = 3
    // B: [(1, 2)] => 1*z[2] = 1*3 = 3
    // C: [(1, 3)] => 1*z[3] = 1*9 = 9

    // Enforces x^3 = x^2 * x
    // A: [(1, 3)] => 1*z[3] = 1*9 = 9
    // B: [(1, 2)] => 1*z[2] = 1*3 = 3
    // C: [(1, 4)] => 1*z[4] = 1*27 = 27

    // Enforces x^3 + x + 5 - y = 0
    // A: [(5, 0), (-1, 1), (1, 2), (1, 4)] => 5*1 + (-1)*35 + 1*3 + 1*27 = 5 - 35 + 3 + 27 = 0
    // B: [(1, 0)] => 1*z[0] = 1*1 = 1
    // C: [] => 0

}