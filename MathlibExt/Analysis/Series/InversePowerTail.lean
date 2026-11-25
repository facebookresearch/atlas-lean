/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Tail bound for inverse powers

Bernoulli's inequality bounds each term strictly by the difference of two consecutive
values of the proposed tail bound. Summing these differences telescopes.
-/

namespace MetaMathlibExt

private theorem tsum_inv_pow_succ_lt.term_lt_sub {x : ℝ} (hx : 0 < x) (d : ℕ)
    (hd : 0 < (d : ℝ)) :
    ((x + 1) ^ (d + 1))⁻¹ < ((d : ℝ) * x ^ d)⁻¹ - ((d : ℝ) * (x + 1) ^ d)⁻¹ := by
  have h : 1 + d / (x + 1) < ((x + 1) / x) ^ d := calc
    1 + d / (x + 1) < 1 + d / x := by
      gcongr
      exact lt_add_one x
    _ ≤ ((x + 1) / x) ^ d := by
      rw [add_div, div_self hx.ne', one_div, div_eq_mul_inv]
      exact one_add_mul_le_pow (by linarith [inv_pos.mpr hx]) d
  rw [div_pow] at h
  rw [pow_succ]
  field_simp at h ⊢
  linarith only [h]

/-- **Tail bound for sums of inverse powers.** For natural numbers $m \ge 2$ and $s \ge 1$,
$\sum_{n = s+1}^{\infty} n^{-m} < \dfrac{1}{(m-1)\, s^{m-1}}$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 42 (`integers-2025-A26-lem-42`). -/
public theorem tsum_inv_pow_succ_lt (m s : ℕ) (hm : 2 ≤ m) (hs : 0 < s) :
    ∑' k : ℕ, (((k + s + 1 : ℕ) : ℝ) ^ m)⁻¹ < (((m - 1 : ℕ) : ℝ) * (s : ℝ) ^ (m - 1))⁻¹ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  have hd : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  let B (k : ℕ) : ℝ := ((d : ℝ) * ((k + s : ℕ) : ℝ) ^ d)⁻¹
  have step (k : ℕ) : (((k + s + 1 : ℕ) : ℝ) ^ (d + 1))⁻¹ < B k - B (k + 1) := by
    simpa [B, Nat.cast_add, add_right_comm] using
      tsum_inv_pow_succ_lt.term_lt_sub (x := (k : ℝ) + s) (by positivity) d hd
  have hsum (n : ℕ) : ∑ k ∈ Finset.range n, (B k - B (k + 1)) ≤ B 0 := by
    rw [Finset.sum_range_sub']
    exact sub_le_self _ (by dsimp [B]; positivity)
  have hB := summable_of_sum_range_le (fun k => le_trans (by positivity) (step k).le) hsum
  calc
    _ < ∑' k : ℕ, (B k - B (k + 1)) :=
      Summable.tsum_lt_tsum_of_nonneg (fun k => by positivity) (fun k => (step k).le) (step 0) hB
    _ ≤ B 0 := hB.tsum_le_of_sum_range_le hsum
    _ = _ := by simp [B]

end MetaMathlibExt
