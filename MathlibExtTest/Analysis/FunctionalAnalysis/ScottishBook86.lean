/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook86

/-! # Tests for the measure and refutation of Scottish Book Problem 86 -/

namespace MathlibExtTest.Analysis.FunctionalAnalysis.ScottishBook86

open MeasureTheory Set
open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook86Wanted

-- The terminal fifth, on which the proof's orthogonal witness is supported, has positive mass.
example : scottishBook86Measure.real (Ioc (4 / 5 : ℝ) 1) = 1 / 5 := by
  have hsub : Ioc (4 / 5 : ℝ) 1 ⊆ Icc 0 1 := fun _ hx => ⟨by linarith [hx.1], hx.2⟩
  rw [scottishBook86Measure, measureReal_restrict_apply measurableSet_Ioc,
    inter_eq_left.mpr hsub, measureReal_def, Real.volume_Ioc]
  norm_num

-- The measure assigns zero mass to the part of the real line outside the unit interval.
example : scottishBook86Measure ((Icc (0 : ℝ) 1)ᶜ) = 0 := by
  rw [scottishBook86Measure, Measure.restrict_apply measurableSet_Icc.compl,
    compl_inter_self, measure_empty]

example : ¬ ScottishBookProblem86Claim :=
  banach86_refuted

end MathlibExtTest.Analysis.FunctionalAnalysis.ScottishBook86
