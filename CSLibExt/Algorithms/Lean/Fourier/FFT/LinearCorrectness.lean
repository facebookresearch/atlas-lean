/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.CircularCorrectness
public import CSLibExt.Algorithms.Lean.Fourier.FFT.PaddingCircular

/-!
# The actual FFT linear result is the complete polynomial product

Both source signs execute the same two materialized zero pads followed by
circular convolution at twice the input length. Every returned coefficient
is the canonical polynomial product coefficient, including the zero final
slot. The represented polynomial equality also checks all higher coefficients.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

/-- Every actual Princeton-sign linear coefficient is the canonical product coefficient. -/
theorem fftLinear_stdAddChar_neg_one_coeff (d : Nat) (xs ys : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ (d + 1))) :
    (fftLinear d (ZMod.stdAddChar (-1 : ZMod (2 ^ (d + 1)))) xs ys).ret[k.val] =
      (fftPolynomial xs * fftPolynomial ys).coeff k.val := by
  rw [fftLinear_ret, fftCircular_stdAddChar_neg_one]
  exact fftPad_circular_coeff_eq_polynomial d xs ys k

/-- The actual Princeton-sign output has the complete source linear coefficient sum. -/
theorem fftLinear_stdAddChar_neg_one_sum (d : Nat) (xs ys : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ (d + 1))) :
    (fftLinear d (ZMod.stdAddChar (-1 : ZMod (2 ^ (d + 1)))) xs ys).ret[k.val] =
      ∑ j ∈ Finset.range (k.val + 1),
        xs.toArray.getD j 0 * ys.toArray.getD (k.val - j) 0 := by
  rw [fftLinear_stdAddChar_neg_one_coeff, fftPolynomial_mul_coeff]

/-- The complete polynomial represented by the actual Princeton-sign return is the product. -/
theorem fftPolynomial_fftLinear_stdAddChar_neg_one (d : Nat)
    (xs ys : Vector ℂ (2 ^ d)) :
    fftPolynomial (fftLinear d (ZMod.stdAddChar (-1 : ZMod (2 ^ (d + 1)))) xs ys).ret =
      fftPolynomial xs * fftPolynomial ys := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < 2 ^ (d + 1)
  · rw [fftPolynomial_coeff]
    rw [← Array.getElem_eq_getD (h := by simpa using hk) 0]
    exact fftLinear_stdAddChar_neg_one_coeff d xs ys ⟨k, hk⟩
  · have hp : 2 * 2 ^ d ≤ k := by
      simpa only [pow_succ, Nat.mul_comm (2 ^ d) 2] using Nat.le_of_not_gt hk
    have hout :
        (fftPolynomial (fftLinear d
          (ZMod.stdAddChar (-1 : ZMod (2 ^ (d + 1)))) xs ys).ret).coeff k = 0 := by
      unfold fftPolynomial
      exact Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk)
    rw [hout, fftPolynomial_mul_coeff_eq_zero_of_two_mul_le xs ys k hp]

/-- The final stored Princeton-sign linear coefficient is zero. -/
theorem fftLinear_stdAddChar_neg_one_last (d : Nat) (xs ys : Vector ℂ (2 ^ d)) :
    (fftLinear d (ZMod.stdAddChar (-1 : ZMod (2 ^ (d + 1)))) xs ys).ret.toArray.getD
      (2 * 2 ^ d - 1) 0 = 0 := by
  have hn : 0 < 2 ^ d := pow_pos (by decide) d
  have hslot : 2 * 2 ^ d - 1 < 2 ^ (d + 1) := by
    simp only [pow_succ]
    omega
  rw [← Array.getElem_eq_getD (h := by simpa using hslot) 0]
  exact (fftLinear_stdAddChar_neg_one_coeff d xs ys
    ⟨2 * 2 ^ d - 1, hslot⟩).trans (fftPolynomial_mul_last d xs ys)

/-- Every actual MIT/CLRS-sign linear coefficient is the canonical product coefficient. -/
theorem fftLinear_stdAddChar_one_coeff (d : Nat) (xs ys : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ (d + 1))) :
    (fftLinear d (ZMod.stdAddChar (1 : ZMod (2 ^ (d + 1)))) xs ys).ret[k.val] =
      (fftPolynomial xs * fftPolynomial ys).coeff k.val := by
  rw [fftLinear_ret, fftCircular_stdAddChar_one]
  exact fftPad_circular_coeff_eq_polynomial d xs ys k

/-- The actual MIT/CLRS-sign output has the complete source linear coefficient sum. -/
theorem fftLinear_stdAddChar_one_sum (d : Nat) (xs ys : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ (d + 1))) :
    (fftLinear d (ZMod.stdAddChar (1 : ZMod (2 ^ (d + 1)))) xs ys).ret[k.val] =
      ∑ j ∈ Finset.range (k.val + 1),
        xs.toArray.getD j 0 * ys.toArray.getD (k.val - j) 0 := by
  rw [fftLinear_stdAddChar_one_coeff, fftPolynomial_mul_coeff]

/-- The complete polynomial represented by the actual MIT/CLRS-sign return is the product. -/
theorem fftPolynomial_fftLinear_stdAddChar_one (d : Nat)
    (xs ys : Vector ℂ (2 ^ d)) :
    fftPolynomial (fftLinear d (ZMod.stdAddChar (1 : ZMod (2 ^ (d + 1)))) xs ys).ret =
      fftPolynomial xs * fftPolynomial ys := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < 2 ^ (d + 1)
  · rw [fftPolynomial_coeff]
    rw [← Array.getElem_eq_getD (h := by simpa using hk) 0]
    exact fftLinear_stdAddChar_one_coeff d xs ys ⟨k, hk⟩
  · have hp : 2 * 2 ^ d ≤ k := by
      simpa only [pow_succ, Nat.mul_comm (2 ^ d) 2] using Nat.le_of_not_gt hk
    have hout :
        (fftPolynomial (fftLinear d
          (ZMod.stdAddChar (1 : ZMod (2 ^ (d + 1)))) xs ys).ret).coeff k = 0 := by
      unfold fftPolynomial
      exact Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk)
    rw [hout, fftPolynomial_mul_coeff_eq_zero_of_two_mul_le xs ys k hp]

/-- The final stored MIT/CLRS-sign linear coefficient is zero. -/
theorem fftLinear_stdAddChar_one_last (d : Nat) (xs ys : Vector ℂ (2 ^ d)) :
    (fftLinear d (ZMod.stdAddChar (1 : ZMod (2 ^ (d + 1)))) xs ys).ret.toArray.getD
      (2 * 2 ^ d - 1) 0 = 0 := by
  have hn : 0 < 2 ^ d := pow_pos (by decide) d
  have hslot : 2 * 2 ^ d - 1 < 2 ^ (d + 1) := by
    simp only [pow_succ]
    omega
  rw [← Array.getElem_eq_getD (h := by simpa using hslot) 0]
  exact (fftLinear_stdAddChar_one_coeff d xs ys
    ⟨2 * 2 ^ d - 1, hslot⟩).trans (fftPolynomial_mul_last d xs ys)

end Cslib.Algorithms.Lean.TimeM
