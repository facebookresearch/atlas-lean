/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GodambeInequality

/-!
# Tests for Godambe's information inequality

On a one-point space with score `s = 2` and estimating function `g = 3` in `E = ℝ`: the bound
is attained (equality case, computed directly), and `inner_inverse_le_integral_inner_sq`
applies with `I = 4`.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace
open MathlibExt.Probability.Statistics.GodambeInequality

namespace MathlibExtTest.Probability.Statistics.GodambeInequality

/-- **Equality case.** On a one-point space with score `s = 2` and estimating function `g = 3`
(so `g ∝ s`) in `E = ℝ`, the information is `I = 4`, `v = E[⟪g, w⟫ s] = 6 w` and
`⟪I⁻¹ v, v⟫ = (6w)² / 4 = 9 w² = E ⟪g, w⟫²`: the bound is attained. -/
example (w : ℝ) : ⟪Ring.inverse ((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
      (∫ _ : Unit, ⟪(3 : ℝ), w⟫ • (2 : ℝ) ∂Measure.dirac ()),
      ∫ _ : Unit, ⟪(3 : ℝ), w⟫ • (2 : ℝ) ∂Measure.dirac ()⟫ = ∫ _ : Unit, ⟪(3 : ℝ), w⟫ ^ 2
        ∂Measure.dirac () := by
  have hI : IsUnit ((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ) :=
    MathlibExt.Probability.Statistics.VectorInference.isUnit_of_inner_self_pos fun u hu => by
      have : 0 < ‖u‖ := norm_pos_iff.2 hu
      simp only [FunLike.coe_smul, ContinuousLinearMap.coe_id', Pi.smul_apply, id_eq,
        real_inner_smul_left, real_inner_self_eq_norm_sq]
      positivity
  have hv : (∫ _ : Unit, ⟪(3 : ℝ), w⟫ • (2 : ℝ) ∂Measure.dirac ()) =
      ((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (3 / 2 * w) := by
    simp; ring
  rw [hv, MathlibExt.Probability.Statistics.VectorInference.inverse_apply_apply hI]
  simp
  ring

example (w : ℝ) : ⟪Ring.inverse ((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
      (∫ _ : Unit, ⟪(3 : ℝ), w⟫ • (2 : ℝ) ∂Measure.dirac ()),
      ∫ _ : Unit, ⟪(3 : ℝ), w⟫ • (2 : ℝ) ∂Measure.dirac ()⟫ ≤ ∫ _ : Unit, ⟪(3 : ℝ), w⟫ ^ 2
        ∂Measure.dirac () := by
  refine inner_inverse_le_integral_inner_sq (s := fun _ => (2 : ℝ)) (g := fun _ => (3 : ℝ))
    aestronglyMeasurable_const (integrable_const _) aestronglyMeasurable_const
    (integrable_const _) ?_ (fun z => ?_) w
  · exact MathlibExt.Probability.Statistics.VectorInference.isUnit_of_inner_self_pos fun u hu => by
      have : 0 < ‖u‖ := norm_pos_iff.2 hu
      simp only [FunLike.coe_smul, ContinuousLinearMap.coe_id', Pi.smul_apply, id_eq,
        real_inner_smul_left, real_inner_self_eq_norm_sq]
      positivity
  · simp; ring

end MathlibExtTest.Probability.Statistics.GodambeInequality
