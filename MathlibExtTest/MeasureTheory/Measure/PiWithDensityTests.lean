/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Measure.PiWithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Tests for products of measures with densities
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace MathlibExtTest.MeasureTheory.PiWithDensity

/-- Three coordinates, each with density `2` on the line, give density `8` on `ℝ³`. -/
example : Measure.pi (fun _ : Fin 3 ↦ volume.withDensity fun _ : ℝ ↦ (2 : ℝ≥0∞)) =
    (Measure.pi fun _ : Fin 3 ↦ (volume : Measure ℝ)).withDensity fun _ ↦ 8 := by
  have : SigmaFinite (volume.withDensity fun _ : ℝ ↦ (2 : ℝ≥0∞)) :=
    SigmaFinite.withDensity_of_ne_top (ae_of_all _ fun _ ↦ ENNReal.ofNat_ne_top)
  rw [Measure.pi_withDensity fun _ ↦ measurable_const]
  congr 1
  funext y
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- Tonelli for products: `3 · 1_[0,1]` in each of two coordinates integrates to `3 · 3`. -/
example : ∫⁻ y, ∏ i : Fin 2, (Set.Icc (0 : ℝ) 1).indicator (fun _ ↦ (3 : ℝ≥0∞)) (y i)
      ∂(Measure.pi fun _ : Fin 2 ↦ (volume : Measure ℝ)) = 9 := by
  rw [lintegral_fintype_prod_eq_prod fun _ ↦ measurable_const.indicator measurableSet_Icc]
  simp only [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one, mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- With no coordinates the product measure is a point mass and the density is `1`. -/
example (μ : Fin 0 → Measure ℝ) [∀ i, SigmaFinite (μ i)] :
    ∫⁻ y, ∏ i, (fun _ : ℝ ↦ (5 : ℝ≥0∞)) (y i) ∂Measure.pi μ = 1 := by
  rw [lintegral_fintype_prod_eq_prod fun _ ↦ measurable_const]
  simp

end MathlibExtTest.MeasureTheory.PiWithDensity
