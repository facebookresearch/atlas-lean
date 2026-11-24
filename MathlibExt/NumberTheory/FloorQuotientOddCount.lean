/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import MathlibExt.NumberTheory.CeilQuotientOddCount
import Mathlib.Algebra.Ring.GeomSum
import MathlibExt.NumberTheory.FloorDivisionCounts

/-!
# The floor parity count as an alternating sum

At each denominator the alternating sum over the thresholds reached by its quotient
is the oddness indicator. Summing by threshold instead counts the denominators for
which the quotient is at least that threshold.
-/

namespace MetaMathlibExt

open Finset

private theorem sum_floor_thresholds {q n : ℕ} (hq : q ≤ n) :
    (∑ d ∈ Icc 1 n, if d ≤ q then (-1 : ℤ) ^ (d + 1) else 0) =
      if Odd q then 1 else 0 := by
  have hfilter : (Icc 1 n).filter (· ≤ q) = Icc 1 q := by
    ext d
    simp only [mem_filter, mem_Icc]
    omega
  rw [← sum_filter, hfilter, ← Ico_succ_right_eq_Icc, sum_Ico_eq_sum_range]
  simp [Nat.add_comm 1, pow_succ, ← Nat.not_even_iff_odd]

/-- **The floor parity count as an alternating sum.** Let $\mathcal{F}_n$ be the number of
integers $k$ with $1 \le k \le n$ for which $\lfloor n/k \rfloor$ is odd. For every natural
number $n$, $\mathcal{F}_n = \sum_{d=1}^{n} \lfloor n/d \rfloor (-1)^{d+1}$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 2 (`jis-2024-24.2.5-prop-2`). -/
public theorem floorQuotientOddCount_eq_alternating_sum (n : ℕ) :
    (floorQuotientOddCount n : ℤ) =
      ∑ d ∈ Finset.Icc 1 n, ((n / d : ℕ) : ℤ) * (-1) ^ (d + 1) := by
  calc
    (floorQuotientOddCount n : ℤ) = ∑ k ∈ Icc 1 n, (if Odd (n / k) then 1 else 0) := by
      simp only [floorQuotientOddCount, sum_boole]
    _ = ∑ d ∈ Icc 1 n, ∑ k ∈ Icc 1 n, if d ≤ n / k then (-1 : ℤ) ^ (d + 1) else 0 := by
      rw [sum_comm]
      exact sum_congr rfl fun k _ => (sum_floor_thresholds (Nat.div_le_self n k)).symm
    _ = _ := by
      refine sum_congr rfl fun d hd => ?_
      rw [← sum_filter, sum_const, floor_div_sequence_card_ge n d (mem_Icc.mp hd).1]
      simp

end MetaMathlibExt
