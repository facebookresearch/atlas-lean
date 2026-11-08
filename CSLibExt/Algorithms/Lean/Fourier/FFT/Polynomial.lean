/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.ConvolutionCharacteristic
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Basic.Complex.Basic
public import Init.Data.Array.Lemmas

/-!
# Canonical input polynomials and actual zero padding

Polynomial.ofFn represents the stored coefficient vector. It supplies a
mathematical specification; the convolution executor continues to operate
on its materialized arrays. Padding preserves this canonical polynomial.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

/-- The canonical polynomial represented by the stored input coefficient vector. -/
noncomputable def fftPolynomial {n : Nat} (xs : Vector ℂ n) : Polynomial ℂ := by
  classical
  exact Polynomial.ofFn n (fun j : Fin n => xs[j.val])

private theorem fft_sample_zero {n : Nat} (xs : Vector ℂ n)
    (k : Nat) (hk : n ≤ k) : xs.toArray.getD k 0 = 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_getElem?]
  rw [dite_eq_right (show ¬ k < xs.toArray.size from by simpa using not_lt_of_ge hk)]

/-- The canonical polynomial's coefficients are exactly the stored zero extension. -/
theorem fftPolynomial_coeff {n : Nat} (xs : Vector ℂ n) (k : Nat) :
    (fftPolynomial xs).coeff k = xs.toArray.getD k 0 := by
  classical
  unfold fftPolynomial
  by_cases hk : k < n
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hk]
    exact Array.getElem_eq_getD (h := by simpa using hk) 0
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk)]
    exact (fft_sample_zero xs k (Nat.le_of_not_gt hk)).symm

/-- Materialized prefix-preserving zero padding represents the same polynomial. -/
theorem fftPolynomial_fftPad (d : Nat) (xs : Vector ℂ (2 ^ d)) :
    fftPolynomial (fftPad d xs).ret = fftPolynomial xs := by
  apply Polynomial.ext
  intro k
  rw [fftPolynomial_coeff, fftPolynomial_coeff]
  by_cases hk : k < 2 ^ d
  · have hkpad : k < 2 ^ (d + 1) := by
      simp only [pow_succ]
      omega
    rw [← Array.getElem_eq_getD (h := by simpa using hkpad) 0,
      ← Array.getElem_eq_getD (h := by simpa using hk) 0]
    exact fftPad_ret_low d xs ⟨k, hk⟩
  · rw [fft_sample_zero xs k (Nat.le_of_not_gt hk)]
    by_cases hkpad : k < 2 ^ (d + 1)
    · rw [← Array.getElem_eq_getD (h := by simpa using hkpad) 0]
      exact fftPad_ret_high d xs ⟨k, hkpad⟩ (Nat.le_of_not_gt hk)
    · exact fft_sample_zero (fftPad d xs).ret k (Nat.le_of_not_gt hkpad)

/-- Canonical polynomial multiplication gives the full source linear coefficient sum. -/
theorem fftPolynomial_mul_coeff {n : Nat} (xs ys : Vector ℂ n) (k : Nat) :
    (fftPolynomial xs * fftPolynomial ys).coeff k =
      ∑ j ∈ Finset.range (k + 1), xs.toArray.getD j 0 * ys.toArray.getD (k - j) 0 := by
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (fftPolynomial xs).coeff i * (fftPolynomial ys).coeff j) k]
  apply Finset.sum_congr rfl
  intro j _
  rw [fftPolynomial_coeff, fftPolynomial_coeff]

/-- The final slot of the twice-sized output polynomial is zero. -/
theorem fftPolynomial_mul_last (d : Nat) (xs ys : Vector ℂ (2 ^ d)) :
    (fftPolynomial xs * fftPolynomial ys).coeff (2 * 2 ^ d - 1) = 0 := by
  rw [fftPolynomial_mul_coeff]
  apply Finset.sum_eq_zero
  intro j _
  have hn : 0 < 2 ^ d := pow_pos (by decide) d
  by_cases hj : j < 2 ^ d
  · have hsub : 2 ^ d ≤ 2 * 2 ^ d - 1 - j := by omega
    rw [fft_sample_zero ys _ hsub, mul_zero]
  · rw [fft_sample_zero xs j (Nat.le_of_not_gt hj), zero_mul]

/-- Every coefficient past the twice-sized output range is zero. -/
theorem fftPolynomial_mul_coeff_eq_zero_of_two_mul_le {n : Nat}
    (xs ys : Vector ℂ n) (k : Nat) (hk : 2 * n ≤ k) :
    (fftPolynomial xs * fftPolynomial ys).coeff k = 0 := by
  rw [fftPolynomial_mul_coeff]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j < n
  · have hsub : n ≤ k - j := by omega
    rw [fft_sample_zero ys _ hsub, mul_zero]
  · rw [fft_sample_zero xs j (Nat.le_of_not_gt hj), zero_mul]

end Cslib.Algorithms.Lean.TimeM
