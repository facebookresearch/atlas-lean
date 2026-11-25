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

-- Boundary check on a nonzero compactly supported function: the
-- indicator of the unit square, applied through the theorem above.
example :
    ∫ p : ℝ × ℝ,
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) p
          ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) =
      ∫ t in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
        ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) (t, y) +
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) (-t, y) +
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) (t, -y) +
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) (-t, -y)) :=
  MeasureTheory.integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections _
    (by
      rw [integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc)]
      exact integrableOn_const (by rw [Measure.prod_prod]; simp))
