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

public import MathlibExt.Analysis.Complex.AnalyticL2.TranslatedAreaMean
public import MathlibExt.Analysis.Complex.AnalyticL2.LocalL2Bound
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Evaluating an analytic L2 representative on a disk

Let `g` be analytic on a planar set `G`, and let `f` be its L2 class for
planar volume restricted to `G`. If the closed disk centered at `a` with
positive radius `r` lies in `G`, then
`|g(a)| ≤ (πr²)^(1/2)/(πr²) ‖f‖₂`. The numerator and denominator are the
actual disk-area constants. The representative equality is almost everywhere
for the restricted measure. Openness or finite total area of `G` is not an
extra hypothesis; the positive-radius closed-disk containment is explicit.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Complex Metric Set

namespace AnalyticL2

/-- At the center of a positive-radius closed disk contained in `G`, an analytic representative is
bounded by the stated square-root-area constant times its L2 class norm.

```lean
theorem norm_point_le (G : Set ℂ) (g : ℂ → ℂ) (hg : AnalyticOn ℂ g G)
    (f : Lp ℂ 2 (volume.restrict G))
    (hfg : ∀ᵐ z ∂volume.restrict G, f z = g z)
    (a : ℂ) (r : ℝ) (hr : 0 < r) (hDisk : closedBall a r ⊆ G) :
    ‖g a‖ ≤ (Real.pi * r ^ 2) ^ (1 / 2 : ℝ) / (Real.pi * r ^ 2) * ‖f‖
``` -/
theorem norm_point_le (G : Set ℂ) (g : ℂ → ℂ) (hg : AnalyticOn ℂ g G)
    (f : Lp ℂ 2 (volume.restrict G))
    (hfg : ∀ᵐ z ∂volume.restrict G, f z = g z)
    (a : ℂ) (r : ℝ) (hr : 0 < r) (hDisk : closedBall a r ⊆ G) :
    ‖g a‖ ≤ (Real.pi * r ^ 2) ^ (1 / 2 : ℝ) / (Real.pi * r ^ 2) * ‖f‖ := by
  have hBall : ball a r ⊆ G := ball_subset_closedBall.trans hDisk
  have hVol : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  have hMeasure : (volume.restrict G) (ball a r) ≠ ⊤ := by
    rw [Measure.restrict_apply isOpen_ball.measurableSet, inter_eq_left.mpr hBall]
    exact ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt
      (isCompact_closedBall a r).measure_lt_top)
  have hReal : (volume.restrict G).real (ball a r) = Real.pi * r ^ 2 := by
    rw [measureReal_def, Measure.restrict_apply isOpen_ball.measurableSet,
      inter_eq_left.mpr hBall, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr.le]
    simp [mul_comm]
  have hMean : (∫ z in ball a r, f z ∂volume.restrict G) =
      (Real.pi * r ^ 2) • g a := by
    rw [Measure.restrict_restrict_of_subset hBall]
    have hAE : ∀ᵐ z ∂volume.restrict (ball a r), f z = g z :=
      ae_restrict_of_ae_restrict_of_subset hBall hfg
    rw [integral_congr_ae hAE]
    exact integral_ball g a r hr (hg.mono hDisk)
  have hEstimate := norm_setIntegral_le (volume.restrict G) (ball a r)
    isOpen_ball.measurableSet hMeasure f
  rw [hMean, hReal, norm_smul, Real.norm_eq_abs, abs_of_pos hVol] at hEstimate
  have hEstimate' : ‖g a‖ * (Real.pi * r ^ 2) ≤
      (Real.pi * r ^ 2) ^ (1 / 2 : ℝ) * ‖f‖ := by
    simpa only [mul_comm] using hEstimate
  have h := (le_div_iff₀ hVol).mpr hEstimate'
  simpa only [mul_div_assoc, div_mul_eq_mul_div] using h

end AnalyticL2

end
