/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Integral.TonelliCounterexample

@[expose] public section

open MeasureTheory Set

namespace MathlibExtTest.MeasureTheory.Integral.TonelliCounterexample

/-- The two iterated integrals of the diagonal indicator differ. -/
example : ∫⁻ x in Icc (0 : ℝ) 1, (∫⁻ y in Icc (0 : ℝ) 1,
      (diagonal ℝ).indicator (1 : ℝ × ℝ → ENNReal) (x, y) ∂Measure.count) ≠
    ∫⁻ y in Icc (0 : ℝ) 1, (∫⁻ x in Icc (0 : ℝ) 1,
      (diagonal ℝ).indicator (1 : ℝ × ℝ → ENNReal) (x, y)) ∂Measure.count := by
  rw [lintegral_lintegral_count_indicator_diagonal, lintegral_count_lintegral_indicator_diagonal]
  exact one_ne_zero

/-- In particular counting measure on `[0, 1]` is not σ-finite (σ-finite measures are s-finite). -/
example : ¬ SigmaFinite ((Measure.count : Measure ℝ).restrict (Icc 0 1)) := fun _ =>
  not_sFinite_count_restrict_Icc inferInstance

/-- With Lebesgue measure on both factors, Tonelli's theorem does apply and both orders give `0`. -/
example : ∫⁻ x in Icc (0 : ℝ) 1, (∫⁻ y in Icc (0 : ℝ) 1,
      (diagonal ℝ).indicator (1 : ℝ × ℝ → ENNReal) (x, y)) =
    ∫⁻ y in Icc (0 : ℝ) 1, (∫⁻ x in Icc (0 : ℝ) 1,
      (diagonal ℝ).indicator (1 : ℝ × ℝ → ENNReal) (x, y)) :=
  lintegral_lintegral_swap ((measurable_one.indicator measurableSet_diagonal).comp
    measurable_id).aemeasurable

end MathlibExtTest.MeasureTheory.Integral.TonelliCounterexample
