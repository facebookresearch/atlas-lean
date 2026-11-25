/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Product identities for HBC calibrating numbers -/

namespace MetaMathlibExt

open Finset

namespace hbcCalibrating_prod_identities

private theorem prod_mul_sub_one (x : ℚ) (j : ℕ) :
    (∏ i ∈ Icc 1 j, (1 + x ^ 2 ^ (i - 1))) * (x - 1) = x ^ 2 ^ j - 1 := by
  rw [← Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
  simpa [add_comm] using (pow_two_pow_sub_pow_two_pow (x := x) (y := 1) j).symm

end hbcCalibrating_prod_identities

open hbcCalibrating_prod_identities

/-- **Product identities for calibrating numbers.** Let $a$ and $d$ be positive integers and let
$k \ge 1$. Put $\alpha = (a + d)/d$, and let $n_i = 1 + \alpha^{2^{i-1}}$ for $1 \le i < k$ and
$n_k = \alpha^{2^{k-1}}$ (the calibrating numbers for $a/(a + d)$). Then
$\prod_{i=1}^{k} (1 - 1/n_i) = a/(a + d)$; for every $j$ with $1 \le j < k$,
$\prod_{i=1}^{j} n_i = (d/a)(\alpha^{2^j} - 1)$; and
$\prod_{i=1}^{k} n_i = (d/a)(\alpha^{2^k} - \alpha^{2^{k-1}})$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 3. -/
public theorem hbcCalibrating_prod_identities (a d k : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hk : 1 ≤ k) :
    let α : ℚ := (a + d) / d
    let n : ℕ → ℚ := fun i => if i < k then 1 + α ^ 2 ^ (i - 1) else α ^ 2 ^ (k - 1)
    ∏ i ∈ Finset.Icc 1 k, (1 - 1 / n i) = (a : ℚ) / (a + d) ∧
      (∀ j, 1 ≤ j → j < k → ∏ i ∈ Finset.Icc 1 j, n i = (d / a) * (α ^ 2 ^ j - 1)) ∧
      ∏ i ∈ Finset.Icc 1 k, n i = (d / a) * (α ^ 2 ^ k - α ^ 2 ^ (k - 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  intro α n
  have hα : 0 < α := div_pos (add_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hd))
    (Nat.cast_pos.mpr hd)
  have hlast : n (m + 1) = α ^ 2 ^ m := by simp [n]
  have hregular {j i : ℕ} (hj : j ≤ m) (hi : i ∈ Icc 1 j) :
      n i = 1 + α ^ 2 ^ (i - 1) :=
    ite_eq_left (Nat.lt_succ_of_le ((mem_Icc.mp hi).2.trans hj))
  have hprefix (j : ℕ) (hj : j ≤ m) :
      ∏ i ∈ Icc 1 j, n i = (d / a : ℚ) * (α ^ 2 ^ j - 1) := by
    have hscale : (d / a : ℚ) * (α - 1) = 1 := by
      dsimp [α]
      field_simp
      ring
    rw [← prod_mul_sub_one, mul_left_comm, hscale, mul_one]
    exact prod_congr rfl (fun i hi => hregular hj hi)
  refine ⟨?_, fun j _ hj => hprefix j (Nat.le_of_lt_succ hj), ?_⟩
  · -- The last factor cancels the reciprocal product from the difference of powers.
    have hrecip (i : ℕ) (hi : i ∈ Icc 1 m) :
        1 - 1 / n i = (1 + α⁻¹ ^ 2 ^ (i - 1))⁻¹ := by
      rw [hregular le_rfl hi, inv_pow]
      have hx : 0 < α ^ 2 ^ (i - 1) := pow_pos hα _
      field_simp
      ring
    rw [prod_Icc_succ_top (by omega), prod_congr rfl hrecip, prod_inv_distrib, hlast]
    have hne : (∏ i ∈ Icc 1 m, (1 + α⁻¹ ^ 2 ^ (i - 1))) ≠ 0 :=
      prod_ne_zero_iff.mpr fun i _ => (add_pos zero_lt_one (pow_pos (inv_pos.mpr hα) _)).ne'
    rw [← one_div, div_mul_eq_mul_div, one_mul, div_eq_iff hne]
    have htarget : (a : ℚ) / (a + d) = 1 - α⁻¹ := by
      dsimp [α]
      field_simp
      ring
    rw [htarget, mul_comm]
    simpa only [mul_sub, mul_one, inv_pow, one_div, neg_sub] using
      congrArg Neg.neg (prod_mul_sub_one α⁻¹ m).symm
  · rw [prod_Icc_succ_top (by omega), hprefix m le_rfl, hlast, Nat.succ_sub_one,
      pow_succ 2, pow_mul]
    ring

end MetaMathlibExt
