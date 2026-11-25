/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.OperatorTheory.LaplaceTransformLpBoundedIffTwo

/-! # Tests for the Laplace transform on the positive half-line -/

open MeasureTheory Set
open scoped ENNReal
open MathlibExt.Analysis.OperatorTheory.LaplaceTransformLpBoundedIffTwoWanted

namespace MathlibExtTest.Analysis.OperatorTheory.LaplaceTransformLpBoundedIffTwo

private noncomputable abbrev ray := volume.restrict (Ici (0 : ℝ))

-- The transform of the unit interval indicator is square integrable.
example : MemLp (fun s : ℝ => ∫ x in Ioc (0 : ℝ) 1, Real.exp (-x * s)) 2 ray := by
  let f := (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))
  have hs : Ioc (0 : ℝ) 1 ⊆ Ici 0 := fun _ hx => hx.1.le
  have hf : MemLp f 2 ray := memLp_indicator_const _ measurableSet_Ioc.nullMeasurableSet _
    (Or.inr (by simp [ray, Measure.restrict_apply, measurableSet_Ioc, inter_eq_left.mpr hs,
      Real.volume_Ioc]))
  obtain ⟨_, _, _, h⟩ := (laplaceTransform_bounded_on_Lp_iff_eq_two 2 (by norm_num)).2 rfl
  have hinterval (s : ℝ) : ∫ x in Ici (0 : ℝ), Real.exp (-x * s) * f x =
      ∫ x in Ioc (0 : ℝ) 1, Real.exp (-x * s) := by
    simp only [f, ← indicator_mul_right (Ioc 0 1) (fun x => Real.exp (-x * s))
      (fun _ => (1 : ℝ)), mul_one, setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr hs]
  simpa only [hinterval] using (h f hf).1

private def boundedAt (p : ℝ≥0∞) : Prop :=
  ∃ C : ℝ≥0∞, 0 < C ∧ C < ⊤ ∧ ∀ f : ℝ → ℝ, MemLp f p ray →
    let L := fun s : ℝ => ∫ x, Real.exp (-x * s) * f x ∂ray
    MemLp L p ray ∧ eLpNorm L p ray ≤ C * eLpNorm f p ray

-- Neither endpoint admits a finite positive uniform bound.
example : ¬boundedAt 1 := by
  intro h
  have := (laplaceTransform_bounded_on_Lp_iff_eq_two 1 le_rfl).1 h
  norm_num at this

example : ¬boundedAt ∞ := by
  intro h
  have := (laplaceTransform_bounded_on_Lp_iff_eq_two ∞ le_top).1 h
  simp at this

end MathlibExtTest.Analysis.OperatorTheory.LaplaceTransformLpBoundedIffTwo
