/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Wavelet.TwoChannelFilterBank

/-!
# Tests for the orthogonal two-channel filter bank

The Haar low-pass filter `h = (δ₀ + δ₁)/√2` on `ℤ / 4` has orthonormal even translates, so the
mirror construction and perfect reconstruction apply to it.
-/

open scoped InnerProductSpace ComplexConjugate
open MathlibExt.Analysis.Wavelet.TwoChannelFilterBank

namespace MathlibExtTest.Analysis.Wavelet.TwoChannelFilterBank

/-- The Haar low-pass filter on `ℤ / 4`. -/
noncomputable def haarLow : EuclideanSpace ℂ (ZMod (2 * 2)) :=
  WithLp.toLp 2 ![(Real.sqrt 2 : ℂ)⁻¹, (Real.sqrt 2 : ℂ)⁻¹, 0, 0]

private lemma sqrt_two_inv_sq : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast
  ring

private lemma sum_zmod_four (f : ZMod (2 * 2) → ℂ) : ∑ k, f k = f 0 + f 1 + f 2 + f 3 :=
  Fin.sum_univ_four f

/-- The even translates of the Haar low-pass filter are orthonormal: the hypothesis of
`orthonormal_filterBankAtoms_mirrorFilter` is satisfiable. -/
theorem haarLow_orthonormal :
    Orthonormal ℂ fun n : Fin 2 => shift (2 * ((n : ℕ) : ZMod (2 * 2))) haarLow := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [inner_shift_shift]
  have e1 : (0 - 2 : ZMod (2 * 2)) = 2 := by decide
  have e2 : (1 - 2 : ZMod (2 * 2)) = 3 := by decide
  have e4 : (3 - 2 : ZMod (2 * 2)) = 1 := by decide
  have e5 : (0 + 2 : ZMod (2 * 2)) = 2 := by decide
  have e6 : (1 + 2 : ZMod (2 * 2)) = 3 := by decide
  have e7 : (2 + 2 : ZMod (2 * 2)) = 0 := by decide
  have e8 : (3 + 2 : ZMod (2 * 2)) = 1 := by decide
  fin_cases m <;> fin_cases n <;> rw [sum_zmod_four] <;>
    simp [haarLow, e1, e2, e4, e5, e6, e7, e8, Complex.conj_ofReal, sqrt_two_inv_sq] <;>
    norm_num

/-- Perfect reconstruction for the Haar filter bank on `ℤ / 4`. -/
example (x : EuclideanSpace ℂ (ZMod (2 * 2))) :
    x = ∑ n : Fin 2, ⟪shift (2 * ((n : ℕ) : ZMod (2 * 2))) haarLow, x⟫_ℂ •
          shift (2 * ((n : ℕ) : ZMod (2 * 2))) haarLow +
        ∑ n : Fin 2, ⟪shift (2 * ((n : ℕ) : ZMod (2 * 2))) (mirrorFilter haarLow), x⟫_ℂ •
          shift (2 * ((n : ℕ) : ZMod (2 * 2))) (mirrorFilter haarLow) :=
  perfect_reconstruction _ _ (orthonormal_filterBankAtoms_mirrorFilter _ haarLow_orthonormal) x

/-- The parity sign is `-1` at `1` and `1` at `2` on `ℤ / 4`. -/
example : paritySign (1 : ZMod (2 * 2)) = -1 ∧ paritySign (2 : ZMod (2 * 2)) = 1 := by
  constructor
  · exact paritySign_one
  · simpa using paritySign_two_mul (N := 2) (1 : ZMod (2 * 2))

end MathlibExtTest.Analysis.Wavelet.TwoChannelFilterBank
