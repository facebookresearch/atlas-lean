/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AdelicCompletionOperations
public import MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Height limit for the completed adelic metric

The heights of the native rational model sequence converge to the computed
quotient height (`heightLimit`).
Modelled on Yuan--Zhang, arXiv:2105.13587v9, Sections 2.5--2.6, 3.4 and 5.3.
The completion is the fixed-gauge completion of `BoundaryMetricCompletionModels`, not
Yuan--Zhang's boundary topology: their adelic line bundles and positivity notions are not
claimed here.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CompletedAdelicPointHeights

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
open MathlibExt.AlgebraicGeometry.BoundaryMetricCompletionModels
open MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights
open MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights
open MeasureTheory Filter
open scoped Topology

private theorem abs_le_of_sub_le {a b g : ℝ} (h : |a - b| ≤ g) : |a| ≤ |b| + g := by
  have htri := abs_add_le (a - b) b
  rw [sub_add_cancel] at htri
  linarith

/-- Heights of the native model sequence converge to the computed quotient height. -/
public theorem heightLimit {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}
    {L : X.left.Modules} (B : EffectiveBoundary A X) (m : BoundaryMetricCompletion (L := L) B)
    {x : BasePoint (K := K) ⟶ X} (F : PointFrame A X L x)
    (D : DominatedApproximation B m F) : HeightConverges B m F D := by
  have hz : ∀ v : A.places, F.vector v (F.basis ()) ≠ 0 := by
    intro v h
    apply F.basis.ne_zero ()
    apply F.injective v
    simpa only [map_zero] using h
  have hpoint : ∀ v : A.places, Tendsto (fun n : ℕ ↦
      MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights.logNorm A X L
      (D.sequence.model n).metric F (F.basis ()) v) atTop
      (𝓝 (MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights.logNorm B m F
        (F.basis ()) v)) := by
    intro v
    have hclass : Quotient.mk _ D.sequence.toCauchy = m := D.class_normalized
    have h := MathlibExt.AlgebraicGeometry.AdelicCompletionEvaluations.logNorm_tendsto B
      D.sequence.toCauchy v (F.point v) (F.vector v (F.basis ()))
    rw [hclass] at h
    exact h
  obtain ⟨N, hN⟩ := D.sequence.cauchy 1 one_pos
  have hbound_int : Integrable (fun v : A.places ↦
      ‖MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights.logNorm A X L
      (D.sequence.model N).metric F (F.basis ()) v‖ + gauge A X B.toBoundary v (F.point v))
      A.measure :=
    (D.model_integrable N).norm.add D.boundary_integrable
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ v : A.places ∂A.measure,
      ‖MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights.logNorm A X L
      (D.sequence.model n).metric F (F.basis ()) v‖ ≤
      ‖MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights.logNorm A X L
      (D.sequence.model N).metric F (F.basis ()) v‖ +
      gauge A X B.toBoundary v (F.point v) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    apply Filter.Eventually.of_forall
    intro v
    have h := hN n N hn le_rfl v (F.point v) (F.vector v (F.basis ())) (hz v)
    simpa only [MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights.logNorm,
      Real.norm_eq_abs, one_mul] using abs_le_of_sub_le h
  have hmeas : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable
      (MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights.logNorm A X L
      (D.sequence.model n).metric F (F.basis ())) A.measure :=
    Filter.Eventually.of_forall fun n ↦ (D.model_integrable n).aestronglyMeasurable
  have hint := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun v : A.places ↦ ‖MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights.logNorm A X L
      (D.sequence.model N).metric F (F.basis ()) v‖ + gauge A X B.toBoundary v (F.point v))
    hmeas hbound hbound_int (Filter.Eventually.of_forall hpoint)
  have hneg := hint.neg
  exact hneg

end WantedExt.AlgebraicGeometry.CompletedAdelicPointHeights
