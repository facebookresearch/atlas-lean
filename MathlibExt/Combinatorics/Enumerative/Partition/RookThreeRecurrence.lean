/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.RookDecomposition
import Mathlib.Tactic.Ring

/-!
# Recurrence for partitions with max-rook number three

Taking coefficients in Sharan's generating function gives a five-term recurrence
beyond the degree of its numerator.
-/

namespace MetaMathlibExt

open PowerSeries

/-- **Linear recurrence for $R_3(n)$.** Let $R_3(n)$ be the number of partitions of $n$ with
max-rook number $3$. For every natural number $n > 14$,
$R_3(n) = 2R_3(n-1) - R_3(n-2) + R_3(n-3) - 2R_3(n-4) + R_3(n-5)$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Corollary 3
(`jis-2026-26.2.6-cor-3`). -/
public theorem maxRookPartitionCount_three_recurrence (n : ℕ) (hn : 14 < n) :
    (maxRookPartitionCount 3 n : ℤ) =
      2 * maxRookPartitionCount 3 (n - 1) - maxRookPartitionCount 3 (n - 2) +
        maxRookPartitionCount 3 (n - 3) - 2 * maxRookPartitionCount 3 (n - 4) +
        maxRookPartitionCount 3 (n - 5) := by
  let F := mk fun k ↦ (maxRookPartitionCount 3 k : ℤ)
  have h : F - 2 • (X ^ 1 * F) + X ^ 2 * F - X ^ 3 * F + 2 • (X ^ 4 * F) - X ^ 5 * F =
      X ^ 6 + 2 • X ^ 7 + X ^ 8 + 2 • X ^ 9 - X ^ 10 - X ^ 12 - X ^ 13 + X ^ 14 := by
    calc
      _ = (1 - X) ^ 3 * (1 + X + X ^ 2) * F := by ring
      _ = _ := by rw [MetaMathlibExt.maxRookPartitionCount_three_genFun]; ring
  have hshift (k : ℕ) (hk : k ≤ 5) :
      coeff n (X ^ k * F) = (maxRookPartitionCount 3 (n - k) : ℤ) := by
    rw [coeff_X_pow_mul', ite_eq_left (by omega : k ≤ n), coeff_mk]
  -- The numerator has no monomial of degree greater than fourteen.
  have hzero (k : ℕ) (hk : k ≤ 14) : coeff n ((X : ℤ⟦X⟧) ^ k) = 0 := by
    rw [coeff_X_pow, ite_eq_right (by omega)]
  have hc := congrArg (coeff n) h
  simp (disch := omega) only [map_add, map_sub, two_nsmul, hshift, hzero] at hc
  simp only [F, coeff_mk] at hc
  omega

end MetaMathlibExt
