/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.JosephusFixedPointRecurrence

open MetaMathlibExt

namespace JosephusFixedPointRecurrenceTest

private instance decidableFixedPoint : DecidablePred IsJosephusThreeFixedPoint :=
  fun n => inferInstanceAs (Decidable (1 ≤ n ∧ josephus 3 n = n))

-- At 1 the valuation is zero, so the next high extremal point is already fixed.
example :
    Nat.nth IsJosephusThreeFixedPoint 1 = 2 ∧
      ((Finset.Ioo 1 (Nat.nth IsJosephusThreeFixedPoint 1)).filter
        (fun n => josephus 3 n + 1 = n)).card = 0 := by
  have ha : Nat.nth IsJosephusThreeFixedPoint 0 = 1 :=
    Nat.nth_count (p := IsJosephusThreeFixedPoint) (n := 1) (by decide)
  have hv : padicValNat 2 (3 * 1 + 2) = 0 := by
    rw [Nat.padicValNat_def]
    exact multiplicity_eq_zero_of_not_dvd (by decide)
  have h := josephusThree_fixedPoint_recurrence 0
  dsimp only at h
  rw [ha, hv] at h
  have hnext := h.2
  change 2 * Nat.nth IsJosephusThreeFixedPoint 1 + 1 = 5 at hnext
  exact ⟨by omega, h.1⟩

-- The valuation at 2 is three, and the next fixed point is 13.
example :
    Nat.nth IsJosephusThreeFixedPoint 2 = 13 ∧
      ((Finset.Ioo 2 (Nat.nth IsJosephusThreeFixedPoint 2)).filter
        (fun n => josephus 3 n + 1 = n)).card = 3 := by
  have ha : Nat.nth IsJosephusThreeFixedPoint 1 = 2 :=
    Nat.nth_count (p := IsJosephusThreeFixedPoint) (n := 2) (by decide)
  have hv : padicValNat 2 (3 * 2 + 2) = 3 := by
    rw [Nat.padicValNat_def]
    let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Nat.multiplicity_prime_pow (p := 2) 3
  have h := josephusThree_fixedPoint_recurrence 1
  dsimp only at h
  rw [ha, hv] at h
  have hnext := h.2
  change 16 * Nat.nth IsJosephusThreeFixedPoint 2 + 8 = 216 at hnext
  exact ⟨by omega, h.1⟩

end JosephusFixedPointRecurrenceTest
