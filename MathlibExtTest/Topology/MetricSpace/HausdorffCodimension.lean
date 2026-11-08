/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.MetricSpace.HausdorffCodimension

/-!
# Tests for `Set.HasHausdorffCodimAtLeast`.
-/

open scoped ENNReal

namespace HausdorffCodimensionTests

theorem t1_empty : (∅ : Set ℝ).HasHausdorffCodimAtLeast 2 3 :=
  Set.hasHausdorffCodimAtLeast_empty 2 3

theorem t2_singleton_not : ¬ ({0} : Set ℝ).HasHausdorffCodimAtLeast 2 3 := by
  intro h
  rcases h with h0 | hle
  · exact Set.singleton_ne_empty 0 h0
  · simp [dimH_singleton] at hle
    have h32 : (3 : ℕ) ≤ 2 := by exact_mod_cast hle
    omega

theorem t2_singleton_yes : ({0} : Set ℝ).HasHausdorffCodimAtLeast 3 3 := by
  refine Or.inr ?_
  simp [dimH_singleton]

theorem t3_truncated : dimH ({0} : Set ℝ) ≤ ((2 - 3 : ℕ) : ℝ≥0∞) := by
  simp [dimH_singleton, show (2 - 3 : ℕ) = 0 from rfl]

theorem t4_univ_yes : (Set.univ : Set ℝ).HasHausdorffCodimAtLeast 1 0 := by
  refine Or.inr ?_
  simp [Real.dimH_univ]

theorem t4_univ_not : ¬ (Set.univ : Set ℝ).HasHausdorffCodimAtLeast 1 1 := by
  intro h
  rcases h with h0 | hle
  · have hm : (0 : ℝ) ∈ (Set.univ : Set ℝ) := Set.mem_univ 0
    rw [h0] at hm
    exact hm
  · rw [Real.dimH_univ] at hle
    norm_cast at hle

theorem t5_range_rat :
    (Set.range ((↑) : ℚ → ℝ)).HasHausdorffCodimAtLeast 1 1 := by
  have hcount : (Set.range ((↑) : ℚ → ℝ)).Countable := by
    have h : (((↑) : ℚ → ℝ) '' Set.univ).Countable :=
      Set.countable_univ.image ((↑) : ℚ → ℝ)
    rwa [Set.image_univ] at h
  have hdim : dimH (Set.range ((↑) : ℚ → ℝ)) = 0 := dimH_countable hcount
  refine Or.inr ?_
  simp [hdim]

theorem t6_mono : ({0} : Set ℝ).HasHausdorffCodimAtLeast 1 0 :=
  t4_univ_yes.mono (Set.subset_univ _)

theorem t6_iff : ({0} : Set ℝ).HasHausdorffCodimAtLeast 3 3 :=
  Set.hasHausdorffCodimAtLeast_iff.mpr
    (Or.inr ⟨by decide, by simp [dimH_singleton]⟩)

theorem t6_empty_of_lt : (∅ : Set ℝ) = ∅ :=
  (Set.hasHausdorffCodimAtLeast_empty 2 3).eq_empty_of_lt (by decide)

theorem t6_of_dimH_le : ({0} : Set ℝ).HasHausdorffCodimAtLeast 1 1 :=
  Set.hasHausdorffCodimAtLeast_of_dimH_le (by decide)
    (by simp [dimH_singleton])

end HausdorffCodimensionTests
