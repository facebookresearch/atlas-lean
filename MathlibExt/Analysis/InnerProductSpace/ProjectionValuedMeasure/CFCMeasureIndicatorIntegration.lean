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

public import MathlibExt.MeasureTheory.Integral.RieszMarkovKakutani.Complex

/-!
# Dominated continuous indicator limits in complex integrals

Let `X` be a compact topological space with its Borel measurable structure, `μ` a complex
measure and `s` a measurable set. Suppose continuous functions `F_n : X → ℂ` satisfy
`|F_n(x)|≤1` and converge to `1_s(x)` for `|μ|`-almost every `x`.

For every bounded measurable `q : X → ℂ`, the integrals converge: `∫ F_n q dμ → ∫ 1_s q dμ`.
This uses the supplied almost-everywhere approximation and does not assert its existence or
require `X` to be Hausdorff.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set
open scoped Topology
open MathlibExt.MeasureTheory.Function
open MathlibExt.MeasureTheory.VectorMeasure
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uX

/-- **Dominated convergence for continuous indicator approximations.** Let `X` be compact with
a topology and its Borel measurable structure, `μ : ComplexMeasure X`, `s ⊆ X` measurable,
and `F_n ∈ C(X,ℂ)` with `|F_n(x)|≤1` for all `n,x`. If `F_n(x)→1_s(x)` for `|μ|`-almost
every `x`, then for every bounded measurable `q`, `complexIntegral μ
(F_n*q)→complexIntegral μ (1_s*q)` as `n→∞`. No Hausdorff assumption is imposed. -/
theorem continuousIndicator_complexIntegral_mul_tendsto {X : Type uX}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : ComplexMeasure X) (s : Set X) (hs : MeasurableSet s)
    (F : ℕ → C(X, ℂ)) (hF : ∀ n x, ‖F n x‖ ≤ 1)
    (hlim : ∀ᵐ x ∂mu.variation,
      Tendsto (fun n => F n x) atTop (𝓝 (s.indicator (fun _ => (1 : ℂ)) x)))
    (q : BoundedMeasurableFunction X) :
    Tendsto (fun n => complexIntegral mu (BoundedMeasurableFunction.ofContinuousMap (F n) * q))
      atTop (𝓝 (complexIntegral mu (BoundedMeasurableFunction.indicator s hs * q))) := by
  let : IsFiniteMeasure mu.variation := ComplexMeasure.isFiniteMeasure_variation mu
  change Tendsto
    (fun n => ∫ᵛ x, (BoundedMeasurableFunction.ofContinuousMap (F n) * q) x
      ∂[ContinuousLinearMap.mul ℝ ℂ; mu]) atTop
    (𝓝 (∫ᵛ x, (BoundedMeasurableFunction.indicator s hs * q) x
      ∂[ContinuousLinearMap.mul ℝ ℂ; mu]))
  apply _root_.MeasureTheory.VectorMeasure.tendsto_integral_of_dominated_convergence
    (fun _ => ‖q‖)
  · intro n
    exact (BoundedMeasurableFunction.ofContinuousMap (F n) * q).measurable.aestronglyMeasurable
  · exact integrable_const ‖q‖
  · intro n
    apply Eventually.of_forall
    intro x
    change ‖F n x * q x‖ ≤ ‖q‖
    calc
      ‖F n x * q x‖ = ‖F n x‖ * ‖q x‖ := norm_mul _ _
      _ ≤ 1 * ‖q‖ :=
        mul_le_mul (hF n x) (q.norm_apply_le_norm x) (norm_nonneg (q x)) zero_le_one
      _ = ‖q‖ := one_mul _
  · filter_upwards [hlim] with x hx
    change Tendsto (fun n => F n x * q x) atTop
      (𝓝 ((BoundedMeasurableFunction.indicator s hs) x * q x))
    rw [BoundedMeasurableFunction.indicator_apply]
    exact hx.mul_const (q x)

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
