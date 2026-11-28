/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.ExactGates


/-!
# Matrix-level Pauli basis changes for exact gates

The matrix-level X/Y basis changes, fair coin, and controlled relative phase over the merged exact Gaussian-rational gate exports. Acceptance-level phase arguments are downstream.
-/

@[expose] public section

open Cslib.Complexity.Classes
namespace Cslib.Complexity.Classes.QuantumGates

set_option autoImplicit false

/-- X basis change B† Z B = X with B = e^{iπ/4}H (global phase cancels) -/
theorem omegaH_conj_zGate : star (complexOfGRatMatrix omegaH) * complexOfGRatMatrix zGate * complexOfGRatMatrix omegaH = complexOfGRatMatrix xGate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, complexOfGRatMatrix,
      omegaH, zGate, xGate, toComplex_gaussRatEnc, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ext_iff] <;>
    norm_num

/-- Y basis change via e^{iπ/4}H S† (target stated as the complex Y matrix; no new Gaussian-rational Y export, avoiding a parallel encoding) -/
theorem omegaH_sDag_conj_zGate : star (complexOfGRatMatrix omegaH * complexOfGRatMatrix sDagGate) * complexOfGRatMatrix zGate * (complexOfGRatMatrix omegaH * complexOfGRatMatrix sDagGate) = !![0, -Complex.I; Complex.I, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, complexOfGRatMatrix,
      omegaH, zGate, sDagGate, toComplex_gaussRatEnc, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ext_iff] <;>
    norm_num

/-- exact fair coin |⟨i|e^{iπ/4}H|0⟩|² = 1/2 -/
theorem normSq_omegaH_apply_zero (i : Fin 2) : Complex.normSq (complexOfGRatMatrix omegaH i 0) = 1 / 2 := by
  fin_cases i <;>
    simp [complexOfGRatMatrix, omegaH, toComplex_gaussRatEnc, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Complex.normSq_mk] <;>
    norm_num

/-- Entries of the encoded phase-shifted Hadamard as the global phase times Hadamard. -/
private theorem toComplex_omegaH_apply (a b : Fin 2) :
    toComplex (omegaH a b) =
      Complex.exp (Real.pi / 4 * Complex.I) * hadamard a b := by
  have h := congrFun (congrFun omegaH_eq_smul_hadamard a) b
  simp only [complexOfGRatMatrix, Matrix.smul_apply, smul_eq_mul] at h
  exact h

/-- matrix half of controlled-label correctness: controlled-(e^{iπ/4}H) = (relative phase e^{iπ/4} on the label-1 branch) · controlled-H (control = low qubit) -/
theorem complexOfGRatMatrix_ctrlLow_omegaH : complexOfGRatMatrix (ctrlLow omegaH) = Matrix.diagonal (fun p : Fin 2 × Fin 2 => if p.1 = 1 then Complex.exp (Real.pi / 4 * Complex.I) else 1) * Matrix.of (fun p q : Fin 2 × Fin 2 => if p.1 = 0 ∧ q.1 = 0 ∧ p.2 = q.2 then 1 else if p.1 = 1 ∧ q.1 = 1 then hadamard p.2 q.2 else 0) := by
  ext p q
  simp only [complexOfGRatMatrix, ctrlLow, Matrix.diagonal_mul, Matrix.of_apply]
  by_cases h1 : p.1 = 0 ∧ q.1 = 0 ∧ p.2 = q.2
  · simp [h1, toComplex_gaussRatEnc, Complex.ext_iff]
  · by_cases h2 : p.1 = 1 ∧ q.1 = 1
    · simp [h2, toComplex_omegaH_apply]
    · by_cases hp : p.1 = 1
      · by_cases hq : q.1 = 1
        · exact absurd ⟨hp, hq⟩ h2
        · simp [hp, hq, toComplex_gaussRatEnc, Complex.ext_iff]
      · simp [h1, hp, toComplex_gaussRatEnc, Complex.ext_iff]

/-- Controlled-`e^{iπ/4} H` with the high qubit as control is `D * C`, with `D` diagonal
(`e^{iπ/4}` where the high bit is `1`) and `C` controlled-`H` with the high qubit as control. -/
theorem complexOfGRatMatrix_ctrlHigh_omegaH : complexOfGRatMatrix (ctrlHigh omegaH) = Matrix.diagonal (fun p : Fin 2 × Fin 2 => if p.2 = 1 then Complex.exp (Real.pi / 4 * Complex.I) else 1) * Matrix.of (fun p q : Fin 2 × Fin 2 => if p.2 = 0 ∧ q.2 = 0 ∧ p.1 = q.1 then 1 else if p.2 = 1 ∧ q.2 = 1 then hadamard p.1 q.1 else 0) := by
  ext p q
  simp only [complexOfGRatMatrix, ctrlHigh, Matrix.diagonal_mul, Matrix.of_apply]
  by_cases h1 : p.2 = 0 ∧ q.2 = 0 ∧ p.1 = q.1
  · simp [h1, toComplex_gaussRatEnc, Complex.ext_iff]
  · by_cases h2 : p.2 = 1 ∧ q.2 = 1
    · simp [h2, toComplex_omegaH_apply]
    · by_cases hp : p.2 = 1
      · by_cases hq : q.2 = 1
        · exact absurd ⟨hp, hq⟩ h2
        · simp [hp, hq, toComplex_gaussRatEnc, Complex.ext_iff]
      · simp [h1, hp, toComplex_gaussRatEnc, Complex.ext_iff]

end Cslib.Complexity.Classes.QuantumGates
