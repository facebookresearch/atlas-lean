/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Multiset.Powerset
import MathlibExt.Combinatorics.BalanceableBoundedPartitions

namespace MathlibExtTest.Combinatorics.BalanceableBoundedPartitions

open MathlibExt.Combinatorics.BalanceableBoundedPartitionsWanted.Combinatorics

-- The first positive size for parts of size at most one is two.
example : Minimal (fun n => 0 < n ∧ ∀ p : n.Partition, Bounded 1 p → Balanceable p) 2 := by
  have h := minimal_balanceable_of_bounded (k := 1) (hk := by decide)
  rwa [show 2 * (Finset.Icc 1 1).lcm id = 2 by decide] at h

-- Four is the first bound covered by the general three-consecutive-integer estimate.
example (p : (24 : ℕ).Partition) (hp : Bounded 4 p) : Balanceable p := by
  have h := (minimal_balanceable_of_bounded 4 (by decide)).1.2
  rw [show 2 * (Finset.Icc 1 4).lcm id = 24 by decide] at h
  exact h p hp

private def partitionOfEight : (8 : ℕ).Partition where
  parts := {3, 3, 2}
  parts_pos := by
    intro i hi
    simp at hi
    omega
  parts_sum := by decide

example : Bounded 3 partitionOfEight := by
  intro i hi
  change i ∈ ({3, 3, 2} : Multiset ℕ) at hi
  simp at hi
  omega

-- Repeated parts count separately. Neither copy of three can be paired to sum to four.
example : ¬ Balanceable partitionOfEight := by
  rintro ⟨s, t, hst, heq⟩
  have hsum := congrArg Multiset.sum hst
  rw [Multiset.sum_add, partitionOfEight.parts_sum, ← heq] at hsum
  have hs : s.sum = 4 := by omega
  have hle : s ≤ partitionOfEight.parts := hst ▸ Multiset.le_add_right _ _
  have hno : ∀ u ∈ partitionOfEight.parts.powerset.toFinset, u.sum ≠ 4 := by decide
  exact hno s (by simpa using hle) hs

end MathlibExtTest.Combinatorics.BalanceableBoundedPartitions
