/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LanglandsTunnell_integral_prod_eq_setIntegral_Ioi_
setIntegral_Ioi_sum_reflections.lean`
and
`P2M/Sol/S_LanglandsTunnell_integral_prod_eq_setIntegral_Ioi_
setIntegral_Ioi_sum_reflections.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory

private theorem integral_eq_setIntegral_Ioi_add_reflection
    (f : ℝ → ℂ) (hf : Integrable f (volume : Measure ℝ)) :
    ∫ t : ℝ, f t = ∫ t in Set.Ioi (0 : ℝ), (f t + f (-t)) := by
  rw [integral_add hf.integrableOn hf.comp_neg.integrableOn, integral_comp_neg_Ioi,
    neg_zero, ← integral_add_compl measurableSet_Ioi hf, compl_Ioi]

/-- The integral of an integrable function on `ℝ × ℝ` is the integral over
the positive quadrant of the sum of its four reflections.

Splitting each real line into its positive and negative halves writes the
integral over the plane as a sum over the four quadrants; the reflections
identify the other three quadrants with the positive one. -/
public theorem integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections
    (F : ℝ × ℝ → ℂ)
    (hF : Integrable F ((volume : Measure ℝ).prod (volume : Measure ℝ))) :
    ∫ p : ℝ × ℝ, F p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) =
      ∫ t in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
        (F (t, y) + F (-t, y) + F (t, -y) + F (-t, -y)) := by
  have eG : ∫ x : ℝ, (∫ y : ℝ, F (x, y)) =
      ∫ t in Set.Ioi (0 : ℝ), ((∫ y : ℝ, F (t, y)) + ∫ y : ℝ, F (-t, y)) :=
    integral_eq_setIntegral_Ioi_add_reflection
      (fun x => ∫ y : ℝ, F (x, y)) hF.integral_prod_left
  rw [integral_prod F hF, eG]
  have h1 : ∀ᵐ t : ℝ, Integrable (fun y : ℝ => F (t, y)) (volume : Measure ℝ) :=
    hF.prod_right_ae
  have h2 : ∀ᵐ t : ℝ, Integrable (fun y : ℝ => F (-t, y)) (volume : Measure ℝ) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h1
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [h1, h2] with t ht1 ht2
  have e1 : ∫ y : ℝ, F (t, y) =
      ∫ y in Set.Ioi (0 : ℝ), (F (t, y) + F (t, -y)) :=
    integral_eq_setIntegral_Ioi_add_reflection _ ht1
  have e2 : ∫ y : ℝ, F (-t, y) =
      ∫ y in Set.Ioi (0 : ℝ), (F (-t, y) + F (-t, -y)) :=
    integral_eq_setIntegral_Ioi_add_reflection _ ht2
  have hA : Integrable (fun y : ℝ => F (t, y) + F (t, -y)) (volume : Measure ℝ) :=
    ht1.add ht1.comp_neg
  have hB : Integrable (fun y : ℝ => F (-t, y) + F (-t, -y)) (volume : Measure ℝ) :=
    ht2.add ht2.comp_neg
  rw [e1, e2, ← integral_add hA.integrableOn hB.integrableOn]
  congr 1
  funext y
  ring

end MeasureTheory
