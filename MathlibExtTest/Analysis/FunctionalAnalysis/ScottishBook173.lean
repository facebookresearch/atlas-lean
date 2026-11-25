/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook173
import MathlibExt.Analysis.InnerProductSpace.LpShiftOperator

open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook173Wanted
open MathlibExt.Analysis.InnerProductSpace.LpShiftOperator

-- Express the refutation using units in the endomorphism ring.
example : ¬ (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
    Dense {T : E →L[ℝ] E | IsUnit T}) := by
  intro h
  apply eidelheit173_refuted
  intro E _ _ _
  exact (h E).mono fun _ hT => isUnit_iff_exists.mp hT

-- The forward shift has a bounded left inverse, yet it fails the two-sided inverse condition.
example : (∃ B, B * shiftCLM (𝕜 := ℝ) = 1) ∧ ¬ IsUnit (shiftCLM (𝕜 := ℝ)) := by
  refine ⟨⟨backwardCLM, backward_comp_shift⟩, ?_⟩
  rintro ⟨u, hu⟩
  exact not_surjective_shiftCLM (𝕜 := ℝ) (hu ▸ (ContinuousLinearEquiv.ofUnit u).surjective)
