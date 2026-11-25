/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.QuantumInformation.Finite.QuantumFourierTransformDFT

/-!
# Tests: the quantum Fourier transform as a discrete Fourier transform
-/

@[expose] public section

namespace MathlibExtTest.QuantumInformation.Finite.QuantumFourierTransformDFT

set_option autoImplicit false

open Matrix
open MathlibExt.QuantumInformation.Finite.QuantumFourierTransform

#print axioms qftMatrix_mulVec_eq_invDFT
#print axioms conjTranspose_qftMatrix_mulVec_eq_dft
#print axioms qftMatrix_two_pow_apply

/-- The `(1, 1)` entry of the four-point transform is `i / 2`. -/
theorem qftMatrix_four_one_one : qftMatrix 4 1 1 = Complex.I / 2 := by
  have v1 : (1 : Fin 4).val = 1 := by simp
  rw [qftMatrix_four]
  simp only [Matrix.of_apply, v1]
  simp

/-- The `(2, 1)` entry of the four-point transform is `-1 / 2`. -/
theorem qftMatrix_four_two_one : qftMatrix 4 2 1 = -(1 / 2 : ℂ) := by
  have v2 : (2 : Fin 4).val = 2 := by simp
  have v1 : (1 : Fin 4).val = 1 := by simp
  rw [qftMatrix_four]
  simp only [Matrix.of_apply, v2, v1]
  norm_num [pow_two, Complex.I_mul_I]

/-- The transform of the constant basis vector `|0⟩` is flat: entry `3` is
`1 / 2` at `q = 4`. -/
theorem qftMatrix_four_mulVec_delta :
    (qftMatrix 4 *ᵥ (fun j : Fin 4 => if j = 0 then (1 : ℂ) else 0)) 3 = 1 / 2 := by
  rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]
  simp only [qftMatrix_four, Matrix.of_apply]
  simp

end MathlibExtTest.QuantumInformation.Finite.QuantumFourierTransformDFT
