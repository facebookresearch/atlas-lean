/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.RookPeriodicity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Parity of the max-rook partition count for rook number three

Modulo two, the count has period six from size ten onward. The generating function
supplies the six initial residues.
-/

namespace MetaMathlibExt

open PowerSeries

private theorem count_coefficient (n : ℕ) :
    let a := fun k : ℕ ↦ (maxRookPartitionCount 3 k : ℤ)
    let shift := fun k : ℕ ↦ if k ≤ n then a (n - k) else 0
    let term := fun k : ℕ ↦ if n = k then (1 : ℤ) else 0
    a n - (shift 1 + shift 1) + shift 2 - shift 3 + (shift 4 + shift 4) - shift 5 =
      term 6 + (term 7 + term 7) + term 8 + (term 9 + term 9) - term 10 - term 12 -
        term 13 + term 14 := by
  let F := mk fun k ↦ (maxRookPartitionCount 3 k : ℤ)
  -- Expand the denominator as a linear combination of shifts of the series.
  have hF : F - 2 • (X ^ 1 * F) + X ^ 2 * F - X ^ 3 * F + 2 • (X ^ 4 * F) - X ^ 5 * F =
      X ^ 6 + 2 • X ^ 7 + X ^ 8 + 2 • X ^ 9 - X ^ 10 - X ^ 12 - X ^ 13 + X ^ 14 := by
    calc
      _ = (1 - X) ^ 3 * (1 + X + X ^ 2) * F := by ring
      _ = _ := by rw [maxRookPartitionCount_three_genFun]; ring
  simpa only [map_sub, map_add, two_nsmul, coeff_X_pow_mul', coeff_X_pow, coeff_mk, F] using
    congrArg (coeff n) hF

private theorem parity_first_period (n : ℕ) (h₁ : 10 ≤ n) (h₂ : n ≤ 15) :
    maxRookPartitionCount 3 n % 2 = if n % 2 = 1 then 0 else 1 := by
  have h := count_coefficient
  dsimp only at h
  generalize maxRookPartitionCount 3 = a at h ⊢
  have c0 := h 0
  have c1 := h 1
  have c2 := h 2
  have c3 := h 3
  have c4 := h 4
  have c5 := h 5
  have c6 := h 6
  have c7 := h 7
  have c8 := h 8
  have c9 := h 9
  have c10 := h 10
  have c11 := h 11
  have c12 := h 12
  have c13 := h 13
  have c14 := h 14
  have c15 := h 15
  norm_num only [ite_true, ite_false, zero_add, add_zero, sub_zero]
    at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
  -- Evaluate the recurrence in order so only the resulting small counts reach the parity check.
  simp_all only [Int.reduceAdd, add_zero, sub_zero]
  interval_cases n <;> norm_num only [ite_true, ite_false] <;> omega

/-- **Parity of $R_3(n)$.** Let $R_3(n)$ be the number of partitions of $n$ with max-rook number
$3$. For every natural number $n > 9$, $R_3(n)$ is even if $n$ is odd and odd if $n$ is even.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 10
(`jis-2026-26.2.6-thm-10`). -/
public theorem maxRookPartitionCount_three_mod_two (n : ℕ) (hn : 9 < n) :
    maxRookPartitionCount 3 n % 2 = if n % 2 = 1 then 0 else 1 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases h : n ≤ 15
    · exact parity_first_period n hn h
    · let k := n - 6
      have hk : 9 < k := by dsimp [k]; omega
      have hkn : k < n := by dsimp [k]; omega
      have hsize : n = k + 6 := by dsimp [k]; omega
      have hperiod := maxRookPartitionCount_three_modEq 2 k (by decide) hk
      change maxRookPartitionCount 3 (k + 6) % 2 = maxRookPartitionCount 3 k % 2 at hperiod
      have hpar : (k + 6) % 2 = k % 2 := by omega
      rw [hsize, hperiod, ih k hkn hk, hpar]

end MetaMathlibExt
