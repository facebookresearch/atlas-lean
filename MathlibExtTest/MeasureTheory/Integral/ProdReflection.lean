/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Integral.ProdReflection

@[expose] public section

open MeasureTheory Set

-- Consumer with the original binders.
example (F : ℝ × ℝ → ℂ)
    (hF : Integrable F ((volume : Measure ℝ).prod (volume : Measure ℝ))) :
    ∫ p : ℝ × ℝ, F p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) =
      ∫ t in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
        (F (t, y) + F (-t, y) + F (t, -y) + F (-t, -y)) :=
  MeasureTheory.integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections F hF

-- The integrability hypothesis matters: the constant function `1` on
-- `ℝ × ℝ` is not integrable with respect to Lebesgue measure.
example : ¬ Integrable (fun _ : ℝ × ℝ => (1 : ℂ))
    ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  rw [integrable_const_iff_isFiniteMeasure one_ne_zero]
  intro h
  have huniv : ((volume : Measure ℝ).prod (volume : Measure ℝ)) Set.univ < ⊤ :=
    IsFiniteMeasure.measure_univ_lt_top
  rw [← Set.univ_prod_univ, Measure.prod_prod] at huniv
  simp at huniv
