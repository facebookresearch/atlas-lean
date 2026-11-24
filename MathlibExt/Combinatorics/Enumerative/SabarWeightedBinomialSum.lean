/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! # Sabar's consecutive weighted binomial sums -/

namespace MetaMathlibExt

-- The finite-sum argument also works at zero; retain the source's domain.
set_option linter.unusedVariables false in
/-- **Consecutive binomial sums weighted by powers of 2.** For a natural number $m$, let
$V_m(2) = \sum_{k=0}^{m} \binom{m+k}{k} 2^k$. For every natural number $n \ge 1$,
$V_n(2) + V_{n+1}(2) = 3 \cdot 2^n \binom{2n+2}{n+1}$.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Lemma 1 (`integers-2026-A27-lem-1`). -/
public theorem sum_choose_mul_two_pow_add_succ (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (n + k).choose k * 2 ^ k +
        ∑ k ∈ Finset.range (n + 2), (n + 1 + k).choose k * 2 ^ k =
      3 * 2 ^ n * (2 * n + 2).choose (n + 1) := by
  let a (k : ℕ) := (n + k).choose k * 2 ^ k
  let b (k : ℕ) := (n + 1 + k).choose k * 2 ^ k
  have hpascal (k : ℕ) : b (k + 1) = a (k + 1) + 2 * b k := by
    dsimp only [a, b]
    rw [Nat.add_right_comm n 1 (k + 1), Nat.choose_succ_succ,
      show n + (k + 1) = n + 1 + k by omega, pow_succ]
    ring
  -- Sum Pascal's identity, restoring the common term at index zero.
  have hsum : ∑ k ∈ Finset.range (n + 1), b k =
      (∑ k ∈ Finset.range (n + 1), a k) + 2 * ∑ k ∈ Finset.range n, b k := by
    rw [Finset.sum_range_succ' b, Finset.sum_range_succ' a]
    simp only [hpascal, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hzero : b 0 = a 0 := by simp [a, b]
    rw [hzero, add_right_comm]
  change (∑ k ∈ Finset.range (n + 1), a k) +
    (∑ k ∈ Finset.range (n + 2), b k) = _
  calc
    -- The common prefix cancels, leaving only the last two terms of `b`.
    _ = 2 * b n + b (n + 1) := by
      rw [Finset.sum_range_succ b n] at hsum
      rw [Finset.sum_range_succ b (n + 1), Finset.sum_range_succ b n]
      omega
    _ = _ := by
      have hcentral : (2 * n + 2).choose (n + 1) =
          2 * (n + 1 + n).choose n := by
        rw [← Nat.add_assoc (2 * n) 1 1, Nat.choose_succ_succ, Nat.choose_symm_half,
          show n + 1 + n = 2 * n + 1 by omega]
        exact (two_mul _).symm
      dsimp only [b]
      rw [show n + 1 + (n + 1) = 2 * n + 2 by omega,
        ← mul_assoc 2 ((n + 1 + n).choose n), ← hcentral, pow_succ]
      ring

end MetaMathlibExt
