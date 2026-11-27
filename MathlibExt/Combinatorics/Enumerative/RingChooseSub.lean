/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Alternating binomial expansion of a shifted binomial coefficient
-/

namespace MetaMathlibExt

open Finset

private lemma choose_reflect (a : ℤ) (r : ℕ) :
    Ring.choose a r = (-1) ^ r * Ring.choose (-a + r - 1) r := by
  simpa only [neg_neg, Units.smul_def, zsmul_eq_mul, Int.cast_id, Int.coe_negOnePow_natCast]
    using Ring.choose_neg (-a) r

/-- **Alternating binomial expansion of a shifted binomial coefficient.** For all natural numbers
$m$, $n$ and $k$,
$$\binom{n+m-k-1}{m} = \sum_{j=0}^{k} (-1)^j \binom{k}{j} \binom{n+m-j-1}{m-j},$$
where, for an integer $x$ and a natural number $i$, $\binom{x}{i} = x(x-1)\cdots(x-i+1)/i!$ is
the generalized binomial coefficient, and the term $\binom{n+m-j-1}{m-j}$ is taken to be $0$
when $j > m$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Lemma 1, Equation (4.10) (`integers-2024-A70-lem-1`). -/
public theorem ringChoose_sub_eq_sum (m n k : ℕ) :
    Ring.choose ((n : ℤ) + m - k - 1) m =
      ∑ j ∈ range (k + 1), (-1) ^ j * (k.choose j : ℤ) *
        (if j ≤ m then Ring.choose ((n : ℤ) + m - j - 1) (m - j) else 0) := by
  -- Reflect the upper argument to expand the sum of k and -n by Vandermonde.
  rw [choose_reflect, show -((n : ℤ) + m - k - 1) + m - 1 = k + -(n : ℤ) by omega,
    Ring.add_choose_eq m (Commute.all _ _), Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    mul_sum]
  simp only [Ring.choose_natCast]
  apply sum_congr_of_eq_on_inter
  · intro j _ hj
    simp only [mem_range, Nat.lt_succ_iff, not_le] at hj
    simp [Nat.choose_eq_zero_of_lt hj]
  · intro j _ hj
    simp only [mem_range, Nat.lt_succ_iff] at hj
    simp [hj]
  · intro j hj _
    have hjm := Nat.le_of_lt_succ (mem_range.mp hj)
    rw [ite_eq_left hjm, choose_reflect ((n : ℤ) + m - j - 1),
      show -((n : ℤ) + m - j - 1) + ↑(m - j) - 1 = -n by omega,
      mul_mul_mul_comm, ← pow_add, Nat.add_sub_of_le hjm]

end MetaMathlibExt
