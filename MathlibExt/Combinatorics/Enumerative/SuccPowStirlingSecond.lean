/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling

/-!
# Powers of a successor via Stirling numbers of the second kind
-/

namespace MetaMathlibExt

open Finset

/-- **Powers of $k + 1$ via Stirling numbers of the second kind.** For all natural numbers $k$
and $\ell$,
$$(k + 1)^\ell = \sum_{j=0}^{k} \binom{k}{j}\, j!\, S(\ell + 1, j + 1),$$
where $S(i, j)$ denotes the Stirling numbers of the second kind.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Lemma 2, Equation (4.11) (`integers-2024-A70-lem-2`). -/
public theorem succ_pow_eq_sum_stirlingSecond (k ℓ : ℕ) :
    (k + 1) ^ ℓ =
      ∑ j ∈ range (k + 1), k.choose j * j.factorial * Nat.stirlingSecond (ℓ + 1) (j + 1) := by
  -- Expand the next power so that shifting the index exposes a common factor of k + 1.
  apply Nat.eq_of_mul_eq_mul_left (n := k + 1) (Nat.succ_pos k)
  rw [← pow_succ', Nat.pow_eq_sum_stirlingSecond_mul_descFactorial,
    sum_range_succ' (fun j => Nat.stirlingSecond (ℓ + 1) j * (k + 1).descFactorial j),
    Nat.stirlingSecond_succ_zero, zero_mul, add_zero, mul_sum]
  apply sum_congr_of_eq_on_inter
  · intro j _ hj
    simp only [mem_range, Nat.lt_succ_iff, not_le] at hj
    rw [Nat.succ_descFactorial_succ, Nat.descFactorial_of_lt hj, mul_zero, mul_zero]
  · intro j _ hj
    simp only [mem_range, Nat.lt_succ_iff, not_le] at hj
    rw [Nat.stirlingSecond_eq_zero_of_lt (Nat.succ_lt_succ hj), mul_zero, mul_zero]
  · intro j _ _
    rw [Nat.succ_descFactorial_succ, Nat.descFactorial_eq_factorial_mul_choose]
    ac_rfl

end MetaMathlibExt
