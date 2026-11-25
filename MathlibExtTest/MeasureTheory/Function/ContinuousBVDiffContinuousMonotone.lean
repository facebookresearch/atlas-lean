/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.ContinuousBVDiffContinuousMonotone
import Mathlib.Analysis.BoundedVariation
import Mathlib.Tactic.Linarith

open Set
open MathlibExt.MeasureTheory.ContinuousBVDiffContinuousMonotoneWanted

private noncomputable def clip (x : ℝ) : ℝ := min (max x 0) 1

private noncomputable def bump (x : ℝ) : ℝ := clip x * (clip x - 1)

-- This continuous function is zero outside [0, 1] and negative in the interior.
example : ∃ F₁ F₂ : ℝ → ℝ,
    Monotone F₁ ∧ Continuous F₁ ∧ Monotone F₂ ∧ Continuous F₂ ∧ bump = F₁ - F₂ := by
  have hmono : Monotone clip := fun _ _ h => min_le_min (max_le_max h le_rfl) le_rfl
  have hcont : Continuous clip := (continuous_id.max continuous_const).min continuous_const
  have hclip₀ (x : ℝ) : 0 ≤ clip x := le_min (le_max_right _ _) zero_le_one
  have hclip₁ (x : ℝ) : clip x ≤ 1 := min_le_right _ _
  have hv : BoundedVariationOn clip univ :=
    (hmono.monotoneOn univ).boundedVariationOn (C := 1) fun x _ =>
      (abs_of_nonneg (hclip₀ x)).symm ▸ hclip₁ x
  have hshift : Monotone (fun x => clip x - 1) :=
    fun _ _ h => sub_le_sub_right (hmono h) 1
  have hvshift : BoundedVariationOn (fun x => clip x - 1) univ :=
    (hshift.monotoneOn univ).boundedVariationOn (C := 1) fun x _ => by
      rw [abs_of_nonpos (sub_nonpos.mpr (hclip₁ x))]
      linarith [hclip₀ x]
  exact exists_continuous_monotone_sub_of_boundedVariationOn (hv.mul hvshift)
    (hcont.mul (hcont.sub continuous_const))
