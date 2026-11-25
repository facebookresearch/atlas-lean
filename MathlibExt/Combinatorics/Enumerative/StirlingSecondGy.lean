/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Gy's inequality for Stirling numbers of the second kind

`MetaMathlibExt.mul_stirlingSecond_sub_gt` compares consecutive Stirling numbers
on a diagonal of fixed positive codimension.
-/

namespace MetaMathlibExt

namespace mul_stirlingSecond_sub_gt

open Nat

-- A partition of n + 1 points into m + 1 blocks has at least 2m + 1 - n singletons.
-- Summing over partitions, a marked singleton can be chosen in (n + 1) S(n, m) ways.
private theorem singleton_bound (n m : ℕ) (hm : m ≤ n) :
    (2 * (m : ℤ) + 1 - n) * stirlingSecond (n + 1) (m + 1) ≤
      ((n : ℤ) + 1) * stirlingSecond n m := by
  induction n generalizing m with
  | zero =>
    obtain rfl : m = 0 := by omega
    decide
  | succ n ih =>
    obtain rfl | hlt := hm.eq_or_lt
    · simp only [stirlingSecond_self, Nat.cast_one, mul_one]
      omega
    cases m with
    | zero =>
      simp only [Nat.cast_zero, mul_zero, zero_add, stirlingSecond_one_right,
        stirlingSecond_succ_zero, Nat.cast_one, mul_one]
      omega
    | succ m =>
      have h₁ := ih m (by omega)
      have h₂ := ih (m + 1) (by omega)
      rw [stirlingSecond_succ_succ (n + 1) (m + 1), stirlingSecond_succ_succ n m]
      rw [stirlingSecond_succ_succ n m] at h₁
      push_cast at h₁ h₂ ⊢
      have hrem : 0 ≤ (n : ℤ) - m - 1 := by omega
      nlinarith only [h₁, mul_le_mul_of_nonneg_left h₂ (show 0 ≤ (m : ℤ) + 1 by positivity),
        mul_nonneg hrem (Nat.cast_nonneg (α := ℤ) (stirlingSecond (n + 1) (m + 2)))]

private theorem stirlingSecond_pos (n m : ℕ) (hm : m + 1 ≤ n) :
    0 < stirlingSecond n (m + 1) := by
  induction n, hm using Nat.le_induction with
  | base => simp [stirlingSecond_self]
  | succ n _ ih =>
    rw [stirlingSecond_succ_succ]
    positivity

end mul_stirlingSecond_sub_gt

/-- **Gy's inequality for Stirling numbers of the second kind.** Let $n$ and $k$ be natural
numbers with $0 < k \le n$, and write $S(m, i)$ for the Stirling number of the second kind, the
number of partitions of an $m$-element set into $i$ nonempty blocks. Then
$(n - 2k)\,S(n + 1, n + 1 - k) < n\,S(n, n - k)$, where the left side is computed in the
integers, so that $n - 2k$ may be negative.

Source: René Gy, *On Certain Products of Three Stirling Numbers*, INTEGERS 26 (2026),
Article A108, Lemma 2.1 (`integers-2026-A108-lem-2-1`). -/
public theorem mul_stirlingSecond_sub_gt {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    ((n : ℤ) - 2 * k) * Nat.stirlingSecond (n + 1) (n + 1 - k) <
      (n : ℤ) * Nat.stirlingSecond n (n - k) := by
  let m := n - k
  have hmk : m + k = n := Nat.sub_add_cancel hkn
  have hidx : n + 1 - k = m + 1 := by omega
  rw [hidx]
  change ((n : ℤ) - 2 * k) * Nat.stirlingSecond (n + 1) (m + 1) <
    (n : ℤ) * Nat.stirlingSecond n m
  have hbound := mul_stirlingSecond_sub_gt.singleton_bound n m (by omega)
  have hpos := mul_stirlingSecond_sub_gt.stirlingSecond_pos n m (by omega)
  have hstep : Nat.stirlingSecond n m < Nat.stirlingSecond (n + 1) (m + 1) := by
    rw [Nat.stirlingSecond_succ_succ]
    exact Nat.lt_add_of_pos_left (Nat.mul_pos (Nat.succ_pos m) hpos)
  have hcoef : 2 * (m : ℤ) + 1 - n = (n : ℤ) - 2 * k + 1 := by omega
  rw [hcoef] at hbound
  have hlt : (Nat.stirlingSecond n m : ℤ) < Nat.stirlingSecond (n + 1) (m + 1) := by
    exact_mod_cast hstep
  linarith only [hbound, hlt]

end MetaMathlibExt
