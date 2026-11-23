/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.DiversityStatistics
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Order.Interval.Finset.Nat

open MathlibExt.Probability.DiversityStatisticsWanted

-- Even with arbitrarily many zero entries, only zero is attained at total zero.
example : giniSimpsonCount 0 = 1 := by
  apply Set.ncard_eq_one.mpr
  refine ⟨0, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    apply List.sum_eq_zero_iff.mpr
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    simp [List.sum_eq_zero_iff.mp hl b hb]
  · exact Set.singleton_subset_iff.mpr ⟨[], rfl, rfl⟩

-- At total two, [1, 1] and [2] realize both values allowed by the bound.
example : giniSimpsonCount 2 = 2 := by
  apply le_antisymm
  · have h := giniSimpsonCount_le 2
    norm_num at h
    exact_mod_cast h
  · let values := {s : ℕ | ∃ l : List ℕ, l.sum = 2 ∧ (l.map (fun a => a ^ 2)).sum = s}
    change 2 ≤ values.ncard
    have hfin : values.Finite := by
      apply (Set.finite_Iic 4).subset
      rintro _ ⟨l, hl, rfl⟩
      calc
        (l.map (fun a => a ^ 2)).sum ≤ (l.map (fun a => 2 * a)).sum := by
          apply List.sum_le_sum
          intro a ha
          simpa only [sq] using Nat.mul_le_mul_right a (hl ▸ List.le_sum_of_mem ha)
        _ = 4 := by simpa [hl] using l.sum_map_mul_left id 2
    have hsub : {2, 4} ⊆ values := by
      refine Set.insert_subset (show 2 ∈ values from ⟨[1, 1], rfl, rfl⟩) ?_
      exact Set.singleton_subset_iff.mpr ⟨[2], rfl, rfl⟩
    simpa [Set.ncard_pair (by decide : (2 : ℕ) ≠ 4)] using Set.ncard_le_ncard hsub hfin
