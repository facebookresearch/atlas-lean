/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Measure.ScottishBook191
import Mathlib.MeasureTheory.Measure.Dirac.Basic

open MeasureTheory MeasurableSpace Set
open MathlibExt.MeasureTheory.ScottishBook191Wanted

example (h : ScottishBookProblem191Claim) : False :=
  szpilrajn191_refuted h

-- For a point mass, the empty family generates every measurable set modulo null sets.
example : IsBase ∅ (Measure.dirac true) := by
  classical
  refine ⟨by simp, ?_, ?_⟩
  · intro s hs
    have hse : s = ∅ := Finset.coe_eq_empty.mp (subset_empty_iff.mp hs)
    simp [hse]
  · intro A _
    by_cases hA : true ∈ A
    · refine ⟨univ, @MeasurableSet.univ _ (generateFrom ∅), ?_⟩
      simp [hA]
    · refine ⟨∅, @MeasurableSet.empty _ (generateFrom ∅), ?_⟩
      simp [hA]

-- A point mass fails the positive-measure splitting condition.
example : ¬ IsConvexMeasure (Measure.dirac true) := by
  intro h
  obtain ⟨B, _, _, hlt, hpos⟩ := h.2 univ MeasurableSet.univ (by simp)
  rcases Measure.dirac_apply_eq_zero_or_one (s := B) (a := true) with hB | hB
  · simp [hB] at hpos
  · simp [hB] at hlt
