/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.GartnerEllis
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.InnerProductSpace.Continuous

/-! Tests for the Gärtner–Ellis theorem on a convergent sequence of point masses. -/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
open MathlibExt.Probability.LargeDeviationPrinciple
open MathlibExt.Probability.LegendreTransform
open MathlibExt.Probability.GartnerEllisWanted

namespace MathlibExtTest.Probability.GartnerEllis

/-- Moving point masses converging to zero have rate zero at the origin and infinity elsewhere. -/
example {d : ℕ} (z : ℕ → EuclideanSpace ℝ (Fin d)) (hz : Tendsto z atTop (𝓝 0)) :
    SatisfiesLDP (fun n => Measure.dirac (z n)) (diracRate 0) ∧
      IsGoodRateFunction (diracRate (0 : EuclideanSpace ℝ (Fin d))) := by
  have hrate : (fun x : EuclideanSpace ℝ (Fin d) =>
      (legendreTransform (fun _ => (0 : EReal)) x).toENNReal) = diracRate 0 := by
    funext x
    by_cases hx : x = 0
    · simp [hx, legendreTransform_zero, diracRate_apply_self]
    · simp [legendreTransform_zero_of_ne hx, diracRate_apply_of_ne hx]
  rw [← hrate]
  apply satisfiesLDP_of_tendsto_scaledCGF (Λ := fun _ => 0)
  · exact fun _ _ => integrable_dirac (by simp)
  · intro t
    have h : Tendsto (fun n => ⟪t, z n⟫_ℝ) atTop (𝓝 0) := by
      simpa only [inner_zero_right] using (tendsto_const_nhds (x := t)).inner hz
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [integral_dirac, Real.log_exp, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr hn.ne')]
  · exact differentiable_const _

end MathlibExtTest.Probability.GartnerEllis
