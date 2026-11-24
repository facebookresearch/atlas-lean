/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.BoundedPuncturedPlaneConst
import Mathlib.Analysis.Calculus.FDeriv.Const

/-! # Tests for constancy on the punctured plane -/

open MathlibExt.Analysis.Complex.BoundedPuncturedPlaneConstWanted

-- A function may take a different value at the puncture.
example :
    let f := Function.update (fun _ : ℂ => (0 : ℂ)) 0 1
    ∃ c : ℂ, Set.EqOn f (fun _ => c) {0}ᶜ ∧ f 0 ≠ c := by
  intro f
  have hoff (z : ℂ) (hz : z ≠ 0) : f z = 0 := Function.update_of_ne hz _ _
  obtain ⟨c, hc⟩ := eqOn_const_of_differentiableOn_compl_zero_of_bounded f
    ((differentiableOn_const 0).congr hoff) ⟨0, fun z hz => by simp [hoff z hz]⟩
  refine ⟨c, hc, ?_⟩
  have hc0 : c = 0 := (hc (show (1 : ℂ) ∈ {0}ᶜ from one_ne_zero)).symm.trans (hoff 1 one_ne_zero)
  simp [f, hc0]
