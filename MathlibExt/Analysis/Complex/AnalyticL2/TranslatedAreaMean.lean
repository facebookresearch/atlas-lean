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

public import MathlibExt.Analysis.Complex.AnalyticL2.AreaMean
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Disk area mean at an arbitrary center

Let `a ∈ ℂ` and `r > 0`. A scalar complex function analytic on the closed
disk centered at `a` has planar Lebesgue integral over the open disk equal
to `π r² • f(a)`. The result retains the original center, positive radius,
open integration disk and closed-disk analyticity assumption.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Complex Metric Set
open scoped Pointwise

namespace AnalyticL2

/-- The planar volume integral over the open disk centered at `a` is `πr²` times the analytic value
at `a`.

```lean
theorem integral_ball (f : ℂ → ℂ) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOn ℂ f (closedBall a r)) :
    (∫ z in ball a r, f z) = (Real.pi * r ^ 2) • f a
``` -/
theorem integral_ball (f : ℂ → ℂ) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOn ℂ f (closedBall a r)) :
    (∫ z in ball a r, f z) = (Real.pi * r ^ 2) • f a := by
  have hg : AnalyticOn ℂ (fun z => f (a + z)) (closedBall 0 r) := by
    have h := (hf.comp_sub (-a)).mono (show closedBall 0 r ⊆ closedBall a r + {-a} from by
      intro z hz
      rw [Set.mem_add]
      refine ⟨a + z, ?_, -a, Set.mem_singleton (-a), ?_⟩
      · simpa only [mem_closedBall, dist_eq_norm, sub_zero, add_sub_cancel_left, mem_closedBall_zero_iff] using hz
      · abel)
    simpa only [sub_neg_eq_add, add_comm] using h
  have hIndicator : (fun z => (ball a r).indicator f (a + z)) =
      (ball (0 : ℂ) r).indicator (fun z => f (a + z)) := by
    funext z
    by_cases hz : z ∈ ball (0 : ℂ) r
    · have ha : a + z ∈ ball a r := by
        simpa only [mem_ball, dist_eq_norm, sub_zero, add_sub_cancel_left, mem_ball_zero_iff] using hz
      rw [Set.indicator_of_mem ha, Set.indicator_of_mem hz]
    · have ha : a + z ∉ ball a r := by
        simpa only [mem_ball, dist_eq_norm, sub_zero, add_sub_cancel_left, mem_ball_zero_iff] using hz
      rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem hz]
  calc
    ∫ z in ball a r, f z = ∫ z, (ball a r).indicator f (a + z) := by
      rw [integral_add_left_eq_self, integral_indicator isOpen_ball.measurableSet]
    _ = ∫ z in ball (0 : ℂ) r, f (a + z) := by
      rw [hIndicator, integral_indicator isOpen_ball.measurableSet]
    _ = (Real.pi * r ^ 2) • f a := by
      simpa only [add_zero] using integral_ball_zero (fun z => f (a + z)) r hr hg

end AnalyticL2

end
