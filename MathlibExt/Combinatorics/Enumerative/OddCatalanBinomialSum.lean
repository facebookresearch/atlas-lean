/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.TouchardCatalanIdentity

/-! # An odd-index binomial sum of Catalan numbers -/

namespace MetaMathlibExt

open Finset

private theorem touchard_rational (m b : ℕ) (hb : m / 2 ≤ b) :
    (catalan (m + 1) : ℚ) =
      ∑ k ∈ range (b + 1), (m.choose (2 * k) : ℚ) * (2 ^ m / 2 ^ (2 * k) * catalan k) := by
  rw [touchard_catalan_identity m, Nat.cast_sum]
  calc
    _ = ∑ k ∈ range (m / 2 + 1),
        (m.choose (2 * k) : ℚ) * (2 ^ m / 2 ^ (2 * k) * catalan k) := by
      refine sum_congr rfl fun k hk => ?_
      have hk' : 2 * k ≤ m := by
        have := mem_range.mp hk
        omega
      push_cast
      rw [pow_sub₀ _ two_ne_zero hk']
      ring
    _ = _ := by
      refine sum_subset (range_mono (Nat.succ_le_succ hb)) fun k _ hk => ?_
      rw [mem_range, not_lt] at hk
      simp [Nat.choose_eq_zero_of_lt (show m < 2 * k by omega)]

/-- **Odd-index binomial sum of Catalan numbers.** Write $C_m = \binom{2m}{m}/(m+1)$ for the
$m$-th Catalan number. For every natural number $n$,
$$\sum_{k=1}^{\lceil n/2 \rceil} \binom{n}{2k-1} \frac{2^n}{2^{2k}} C_k =
\frac{1}{2} C_{n+2} - C_{n+1}.$$

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 1 (`integers-2026-A19-prop-1`). -/
public theorem sum_choose_odd_two_pow_mul_catalan (n : ℕ) :
    ∑ k ∈ Icc 1 ((n + 1) / 2), (n.choose (2 * k - 1) : ℚ) * 2 ^ n / 2 ^ (2 * k) * catalan k =
      catalan (n + 2) / 2 - catalan (n + 1) := by
  let b := (n + 1) / 2
  let w (k : ℕ) : ℚ := 2 ^ (n + 1) / 2 ^ (2 * k) * catalan k
  have hs : (catalan (n + 2) : ℚ) = ∑ k ∈ range (b + 1), ((n + 1).choose (2 * k) : ℚ) * w k :=
    touchard_rational (n + 1) b le_rfl
  -- Pad the row for `n` by zero. At `2 * k = n + 1` its even binomial coefficient
  -- vanishes, but the odd coefficient from Pascal's rule survives with weight `C_k / 2`.
  have hn : 2 * (catalan (n + 1) : ℚ) =
      ∑ k ∈ range (b + 1), (n.choose (2 * k) : ℚ) * w k := by
    rw [touchard_rational n b (by dsimp only [b]; omega), mul_sum]
    refine sum_congr rfl fun k _ => ?_
    dsimp only [w]
    rw [pow_succ]
    ring
  let d (k : ℕ) : ℚ :=
    (((n + 1).choose (2 * k) : ℚ) * w k - (n.choose (2 * k) : ℚ) * w k) / 2
  calc
    _ = ∑ k ∈ Icc 1 b, d k := by
      refine sum_congr rfl fun k hk => ?_
      have hk' := (mem_Icc.mp hk).1
      have hidx : 2 * k - 1 + 1 = 2 * k := by omega
      have hchoose := Nat.choose_succ_succ' n (2 * k - 1)
      rw [hidx] at hchoose
      dsimp only [d, w]
      rw [hchoose, Nat.cast_add, pow_succ]
      ring
    _ = ∑ k ∈ range (b + 1), d k := by
      refine sum_subset (fun k hk => mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hk).2)) ?_
      intro k hk hk'
      simp only [mem_range] at hk
      simp only [mem_Icc] at hk'
      have hzero : k = 0 := by omega
      subst k
      simp [d]
    _ = _ := by
      dsimp only [d]
      rw [← sum_div, sum_sub_distrib, ← hs, ← hn]
      ring

end MetaMathlibExt
