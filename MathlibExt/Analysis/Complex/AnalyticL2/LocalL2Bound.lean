/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Integrating a scalar L2 class over a finite-measure set

For any measurable space `α`, measure `μ`, measurable set `s` with
`μ(s) < ∞`, and scalar complex L2 class `f`, the set integral satisfies
`|∫s f dμ| ≤ μ(s)^(1/2) ‖f‖₂`. The real measure is `μ.real s` and the
norm is the original `Lp ℂ 2 μ` norm. Zero-measure and empty sets are
included; neither finite total measure nor probability normalization is
assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace AnalyticL2

/-- A scalar L2 set integral on a measurable finite-measure set is bounded by the square root of
that set measure times the original L2 norm.

```lean
theorem norm_setIntegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (f : Lp ℂ 2 μ) :
    ‖∫ x in s, f x ∂μ‖ ≤ μ.real s ^ (1 / 2 : ℝ) * ‖f‖
``` -/
theorem norm_setIntegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (f : Lp ℂ 2 μ) :
    ‖∫ x in s, f x ∂μ‖ ≤ μ.real s ^ (1 / 2 : ℝ) * ‖f‖ := by
  rw [← L2.inner_indicatorConstLp_one hs hμs f]
  calc
    ‖inner ℂ (indicatorConstLp 2 hs hμs (1 : ℂ)) f‖ ≤
        ‖indicatorConstLp 2 hs hμs (1 : ℂ)‖ * ‖f‖ := norm_inner_le_norm _ _
    _ = μ.real s ^ (1 / 2 : ℝ) * ‖f‖ := by
      rw [norm_indicatorConstLp (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
      simp only [norm_one, one_mul, ENNReal.toReal_ofNat]

end AnalyticL2

end
