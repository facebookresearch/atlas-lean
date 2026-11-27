/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.PauliBasisChange

/-!
# Tests: Matrix-level Pauli basis changes for exact gates
-/

@[expose] public section

open Cslib.Complexity.Classes
namespace CslibTest.Complexity.Classes.QuantumGates

set_option autoImplicit false

open Cslib.Complexity.Classes.QuantumGates

/-- Entry (0, 0) of the X basis-change identity. -/
theorem omegaH_conj_zGate_entry_00 :
    (star (complexOfGRatMatrix omegaH) * complexOfGRatMatrix zGate *
      complexOfGRatMatrix omegaH) 0 0 = 0 := by
  simp [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, complexOfGRatMatrix,
    omegaH, zGate, toComplex_gaussRatEnc, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ext_iff] <;> norm_num

/-- Entry (0, 1) of the X basis-change identity. -/
theorem omegaH_conj_zGate_entry_01 :
    (star (complexOfGRatMatrix omegaH) * complexOfGRatMatrix zGate *
      complexOfGRatMatrix omegaH) 0 1 = 1 := by
  simp [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, complexOfGRatMatrix,
    omegaH, zGate, toComplex_gaussRatEnc, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ext_iff] <;> norm_num

/-- Entry (1, 0) of the X basis-change identity. -/
theorem omegaH_conj_zGate_entry_10 :
    (star (complexOfGRatMatrix omegaH) * complexOfGRatMatrix zGate *
      complexOfGRatMatrix omegaH) 1 0 = 1 := by
  simp [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, complexOfGRatMatrix,
    omegaH, zGate, toComplex_gaussRatEnc, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ext_iff] <;> norm_num

/-- Entry (1, 1) of the X basis-change identity. -/
theorem omegaH_conj_zGate_entry_11 :
    (star (complexOfGRatMatrix omegaH) * complexOfGRatMatrix zGate *
      complexOfGRatMatrix omegaH) 1 1 = 0 := by
  simp [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, complexOfGRatMatrix,
    omegaH, zGate, toComplex_gaussRatEnc, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ext_iff] <;> norm_num

/-- Entry (0, 0) of the Y basis-change identity. -/
theorem omegaH_sDag_conj_zGate_entry_00 :
    (star (complexOfGRatMatrix omegaH * complexOfGRatMatrix sDagGate) *
      complexOfGRatMatrix zGate *
      (complexOfGRatMatrix omegaH * complexOfGRatMatrix sDagGate)) 0 0 = 0 := by
  simp [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, complexOfGRatMatrix,
    omegaH, zGate, sDagGate, toComplex_gaussRatEnc, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ext_iff] <;> norm_num

/-- Entry (0, 1) of the Y basis-change identity. -/
theorem omegaH_sDag_conj_zGate_entry_01 :
    (star (complexOfGRatMatrix omegaH * complexOfGRatMatrix sDagGate) *
      complexOfGRatMatrix zGate *
      (complexOfGRatMatrix omegaH * complexOfGRatMatrix sDagGate)) 0 1 =
      -Complex.I := by
  simp [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, complexOfGRatMatrix,
    omegaH, zGate, sDagGate, toComplex_gaussRatEnc, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ext_iff] <;> norm_num

/-- Entry (1, 0) of the Y basis-change identity. -/
theorem omegaH_sDag_conj_zGate_entry_10 :
    (star (complexOfGRatMatrix omegaH * complexOfGRatMatrix sDagGate) *
      complexOfGRatMatrix zGate *
      (complexOfGRatMatrix omegaH * complexOfGRatMatrix sDagGate)) 1 0 =
      Complex.I := by
  simp [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, complexOfGRatMatrix,
    omegaH, zGate, sDagGate, toComplex_gaussRatEnc, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ext_iff] <;> norm_num

/-- Entry (1, 1) of the Y basis-change identity. -/
theorem omegaH_sDag_conj_zGate_entry_11 :
    (star (complexOfGRatMatrix omegaH * complexOfGRatMatrix sDagGate) *
      complexOfGRatMatrix zGate *
      (complexOfGRatMatrix omegaH * complexOfGRatMatrix sDagGate)) 1 1 = 0 := by
  simp [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, complexOfGRatMatrix,
    omegaH, zGate, sDagGate, toComplex_gaussRatEnc, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ext_iff] <;> norm_num

#print axioms omegaH_conj_zGate
#print axioms omegaH_sDag_conj_zGate
#print axioms complexOfGRatMatrix_ctrlLow_omegaH
#print axioms complexOfGRatMatrix_ctrlHigh_omegaH

end CslibTest.Complexity.Classes.QuantumGates
