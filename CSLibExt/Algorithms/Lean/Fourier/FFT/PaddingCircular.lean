/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.Polynomial
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.BigOperators

/-! # Zero padding removes the circular wraparound terms -/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

private theorem fft_wrap_index_ge (d : Nat) (k j : Nat)
    (hj : j < 2 ^ d) (hkj : k < j) :
    2 ^ d ≤ ((k : ZMod (2 ^ (d + 1))) - (j : ZMod (2 ^ (d + 1)))).val := by
  have hjpad : j < 2 ^ (d + 1) := by
    simp only [pow_succ]
    omega
  have hkpad : k < 2 ^ (d + 1) := lt_trans hkj hjpad
  have hsub : ((j : ZMod (2 ^ (d + 1))) - (k : ZMod (2 ^ (d + 1)))).val = j - k := by
    rw [ZMod.val_sub (by
      rw [ZMod.val_natCast_of_lt hkpad, ZMod.val_natCast_of_lt hjpad]
      omega), ZMod.val_natCast_of_lt hjpad, ZMod.val_natCast_of_lt hkpad]
  have hne : (j : ZMod (2 ^ (d + 1))) - (k : ZMod (2 ^ (d + 1))) ≠ 0 := by
    intro hz
    have hv := congrArg (fun x : ZMod (2 ^ (d + 1)) => x.val) hz
    rw [hsub, ZMod.val_zero] at hv
    omega
  let : NeZero ((j : ZMod (2 ^ (d + 1))) - (k : ZMod (2 ^ (d + 1)))) := ⟨hne⟩
  rw [← neg_sub (j : ZMod (2 ^ (d + 1))) (k : ZMod (2 ^ (d + 1))),
    ZMod.val_neg_of_ne_zero, hsub, pow_succ]
  omega

private theorem fft_finEquiv_natCast (n : Nat) [NeZero n] (j : Fin n) :
    ZMod.finEquiv n j = (j.val : ZMod n) := by
  have hval : (ZMod.finEquiv n j).val = j.val := by
    cases n with
    | zero => exact (NeZero.ne (0 : Nat) rfl).elim
    | succ n => rfl
  exact (ZMod.natCast_zmod_val (ZMod.finEquiv n j)).symm.trans
    (congrArg (fun k : Nat => (k : ZMod n)) hval)

private theorem fftPad_getD (d : Nat) (xs : Vector ℂ (2 ^ d)) (k : Nat) :
    (fftPad d xs).ret.toArray.getD k 0 = xs.toArray.getD k 0 := by
  have h := congrArg (fun p : Polynomial ℂ => p.coeff k) (fftPolynomial_fftPad d xs)
  simpa only [fftPolynomial_coeff] using h

private theorem fft_vector_sample_zero {n : Nat} (xs : Vector ℂ n)
    (k : Nat) (hk : n ≤ k) : xs.toArray.getD k 0 = 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_getElem?]
  rw [dite_eq_right (show ¬ k < xs.toArray.size from by simpa using not_lt_of_ge hk)]

private theorem fft_circular_summand (d : Nat) (xs ys : Vector ℂ (2 ^ d))
    (k j : Nat) (hk : k < 2 ^ (d + 1)) (hj : j < 2 ^ (d + 1)) :
    xs.toArray.getD j 0 *
      ys.toArray.getD ((k : ZMod (2 ^ (d + 1))) - (j : ZMod (2 ^ (d + 1)))).val 0 =
      if j ≤ k then xs.toArray.getD j 0 * ys.toArray.getD (k - j) 0 else 0 := by
  by_cases hjk : j ≤ k
  · rw [ite_eq_left hjk, ZMod.val_sub (by
      rw [ZMod.val_natCast_of_lt hj, ZMod.val_natCast_of_lt hk]
      exact hjk), ZMod.val_natCast_of_lt hk, ZMod.val_natCast_of_lt hj]
  · rw [ite_eq_right hjk]
    by_cases hsmall : j < 2 ^ d
    · rw [fft_vector_sample_zero ys _
        (fft_wrap_index_ge d k j hsmall (Nat.lt_of_not_ge hjk)), mul_zero]
    · rw [fft_vector_sample_zero xs j (Nat.le_of_not_gt hsmall), zero_mul]

/-- Actual stored zero padding makes every cyclic coefficient a linear product coefficient. -/
theorem fftPad_circular_coeff_eq_polynomial (d : Nat) (xs ys : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ (d + 1))) :
    (∑ j : ZMod (2 ^ (d + 1)), (fftPad d xs).ret.toArray.getD j.val 0 *
      (fftPad d ys).ret.toArray.getD ((k.val : ZMod (2 ^ (d + 1))) - j).val 0) =
      (fftPolynomial xs * fftPolynomial ys).coeff k.val := by
  classical
  rw [fftPolynomial_mul_coeff]
  simp_rw [fftPad_getD]
  calc
    (∑ j : ZMod (2 ^ (d + 1)), xs.toArray.getD j.val 0 *
      ys.toArray.getD ((k.val : ZMod (2 ^ (d + 1))) - j).val 0) =
        ∑ j : Fin (2 ^ (d + 1)),
          if j.val ≤ k.val then
            xs.toArray.getD j.val 0 * ys.toArray.getD (k.val - j.val) 0 else 0 := by
      rw [← Equiv.sum_comp (ZMod.finEquiv (2 ^ (d + 1))).toEquiv
        (fun j : ZMod (2 ^ (d + 1)) => xs.toArray.getD j.val 0 *
          ys.toArray.getD ((k.val : ZMod (2 ^ (d + 1))) - j).val 0)]
      apply Finset.sum_congr rfl
      intro j _
      change xs.toArray.getD (ZMod.finEquiv (2 ^ (d + 1)) j).val 0 *
          ys.toArray.getD ((k.val : ZMod (2 ^ (d + 1))) -
            ZMod.finEquiv (2 ^ (d + 1)) j).val 0 =
        if j.val ≤ k.val then
          xs.toArray.getD j.val 0 * ys.toArray.getD (k.val - j.val) 0 else 0
      rw [fft_finEquiv_natCast (2 ^ (d + 1)) j, ZMod.val_natCast_of_lt j.isLt]
      exact fft_circular_summand d xs ys k.val j.val k.isLt j.isLt
    _ = ∑ j ∈ Finset.range (2 ^ (d + 1)),
          if j ≤ k.val then xs.toArray.getD j 0 * ys.toArray.getD (k.val - j) 0 else 0 :=
      Fin.sum_univ_eq_sum_range
        (fun j : Nat => if j ≤ k.val then
          xs.toArray.getD j 0 * ys.toArray.getD (k.val - j) 0 else (0 : ℂ))
        (2 ^ (d + 1))
    _ = ∑ j ∈ Finset.range (k.val + 1),
          if j ≤ k.val then xs.toArray.getD j 0 * ys.toArray.getD (k.val - j) 0 else 0 := by
      apply (Finset.sum_subset
        (Finset.range_mono (Nat.succ_le_of_lt k.isLt)) ?_).symm
      intro j _ hj
      have hle : ¬ j ≤ k.val := by
        intro h
        exact hj (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
      exact ite_eq_right hle
    _ = ∑ j ∈ Finset.range (k.val + 1),
          xs.toArray.getD j 0 * ys.toArray.getD (k.val - j) 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

end Cslib.Algorithms.Lean.TimeM
