/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Normed.Module.FiniteDimension
import MathlibExt.Analysis.FunctionalAnalysis.ClosedL2SubspaceOfContinuousFiniteDim

open MeasureTheory
open scoped ENNReal
open MathlibExt.Analysis.FunctionalAnalysis.ClosedL2SubspaceOfContinuousFiniteDimWanted

/-- The criterion applies to the span of the class of the coordinate function. -/
example :
    let A := ContinuousMap.toLp (E := ℝ) (p := (2 : ENNReal))
      (volume : Measure (Set.Icc (0 : ℝ) 1)) ℝ
    let f : C(Set.Icc (0 : ℝ) 1, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
    FiniteDimensional ℝ ↥(ℝ ∙ A f) := by
  let A := ContinuousMap.toLp (E := ℝ) (p := (2 : ENNReal))
    (volume : Measure (Set.Icc (0 : ℝ) 1)) ℝ
  let f : C(Set.Icc (0 : ℝ) 1, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  change FiniteDimensional ℝ ↥(ℝ ∙ A f)
  apply finiteDimensional_of_isClosed_of_le_range_toLp
  · exact Submodule.isClosed_of_finiteDimensional _
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨f, rfl⟩
