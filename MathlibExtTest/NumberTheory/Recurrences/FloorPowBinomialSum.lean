/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.FloorPowBinomialSum

namespace MetaMathlibExt

open Finset

-- At ℓ = 1 the floor disappears and the recurrence has multiplier 1 + t.
example {R : Type*} [CommRing R] (t : R) (n : ℕ) :
    let T (m : ℕ) := ∑ j ∈ range (m + 1), (m.choose j : R) * t ^ j
    T (n + 1) = (1 + t) * T n := by
  intro T
  rw [add_mul, one_mul, ← sub_eq_iff_eq_add', ← sub_eq_zero]
  simpa only [T, sum_range_succ _ 1, sum_range_one, Nat.choose_zero_right, Nat.choose_self,
    Nat.cast_one, pow_zero, pow_one, one_mul, neg_one_mul, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, sub_eq_add_neg] using floorPowBinomialSum_recurrence t (ℓ := 1) le_rfl n

-- At the initial index the alternating sum is t, since the initial binomial row sums to one.
example {R : Type*} [CommRing R] (t : R) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ∑ i ∈ range (ℓ + 1), (ℓ.choose i : R) * (-1) ^ i *
        ∑ j ∈ range (ℓ - i + 1), ((ℓ - i).choose j : R) * t ^ (j / ℓ) = t := by
  simpa using sub_eq_zero.mp (floorPowBinomialSum_recurrence t hℓ 0)

end MetaMathlibExt
