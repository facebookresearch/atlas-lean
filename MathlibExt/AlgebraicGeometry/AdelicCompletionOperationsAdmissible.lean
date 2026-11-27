/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights
import MathlibExt.AlgebraicGeometry.AdelicCompletionEvaluations
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith

/-!
# Admissibility from dominated model approximation

A dominated model approximation makes the completed point height
admissible: the integrable model log norms and the integrable boundary
gauge dominate the limit log norms.

Modelled on Yuan--Zhang, arXiv:2105.13587v9, Sections 2.5--2.6, 3.4 and 5.3.
The completion is the fixed-gauge completion of `BoundaryMetricCompletionModels`, not
Yuan--Zhang's boundary topology: their adelic line bundles and positivity notions are not
claimed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CompletedAdelicPointHeights

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
open MathlibExt.AlgebraicGeometry.BoundaryMetricCompletionModels
open MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights
open MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights
open MeasureTheory Filter
open scoped Topology

/-- The integrable model norms and actual integrable boundary gauge dominate the limit. -/
public theorem admissible {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}
    {L : X.left.Modules} (B : EffectiveBoundary A X) (m : BoundaryMetricCompletion (L := L) B)
    {x : BasePoint (K := K) ⟶ X} (F : PointFrame A X L x)
    (D : DominatedApproximation B m F) : IsAdmissible B m F := by
  intro e he
  obtain ⟨N, hN⟩ := D.sequence.cauchy 1 one_pos
  have ht : ∀ v, Tendsto
      (fun n ↦ MeasuredLinePointHeights.logNorm A X L (D.sequence.model n).metric F
        (F.basis ()) v)
      atTop (𝓝 (CompletedAdelicPointHeights.logNorm B m F (F.basis ()) v)) := by
    intro v
    have h := AdelicCompletionEvaluations.logNorm_tendsto B D.sequence.toCauchy v
      (F.point v) (F.vector v (F.basis ()))
    have hmk : D.sequence.class = Quotient.mk _ D.sequence.toCauchy := rfl
    rw [← hmk, D.class_normalized] at h
    exact h
  have hlim : ∀ᵐ v ∂A.measure, Tendsto
      (fun n ↦ MeasuredLinePointHeights.logNorm A X L (D.sequence.model n).metric F
        (F.basis ()) v)
      atTop (𝓝 (CompletedAdelicPointHeights.logNorm B m F (F.basis ()) v)) :=
    Eventually.of_forall ht
  have hdom : ∀ᵐ v ∂A.measure,
      ‖CompletedAdelicPointHeights.logNorm B m F (F.basis ()) v‖ ≤
        ‖MeasuredLinePointHeights.logNorm A X L (D.sequence.model N).metric F
          (F.basis ()) v‖ + gauge A X B.toBoundary v (F.point v) := by
    filter_upwards [] with v
    have hz : F.vector v (F.basis ()) ≠ 0 := by
      intro h
      apply F.basis.ne_zero ()
      apply F.injective v
      simpa only [map_zero] using h
    have hT : Tendsto
        (fun n ↦ |MeasuredLinePointHeights.logNorm A X L (D.sequence.model n).metric F
          (F.basis ()) v - MeasuredLinePointHeights.logNorm A X L
          (D.sequence.model N).metric F (F.basis ()) v|)
        atTop
        (𝓝 |CompletedAdelicPointHeights.logNorm B m F (F.basis ()) v -
          MeasuredLinePointHeights.logNorm A X L (D.sequence.model N).metric F
            (F.basis ()) v|) :=
      ((ht v).sub tendsto_const_nhds).abs
    have hev : ∀ᶠ n in atTop,
        |MeasuredLinePointHeights.logNorm A X L (D.sequence.model n).metric F
            (F.basis ()) v -
          MeasuredLinePointHeights.logNorm A X L (D.sequence.model N).metric F
            (F.basis ()) v| ≤ 1 * gauge A X B.toBoundary v (F.point v) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      exact hN n N hn le_rfl v (F.point v) (F.vector v (F.basis ())) hz
    have hle := le_of_tendsto hT hev
    have h1 := abs_sub_abs_le_abs_sub
      (CompletedAdelicPointHeights.logNorm B m F (F.basis ()) v)
      (MeasuredLinePointHeights.logNorm A X L (D.sequence.model N).metric F (F.basis ()) v)
    simp only [Real.norm_eq_abs]
    linarith
  have hmeas : AEStronglyMeasurable
      (CompletedAdelicPointHeights.logNorm B m F (F.basis ())) A.measure :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (D.model_integrable n).aestronglyMeasurable) hlim
  have hbound : Integrable
      (fun v ↦ ‖MeasuredLinePointHeights.logNorm A X L (D.sequence.model N).metric F
        (F.basis ()) v‖ + gauge A X B.toBoundary v (F.point v)) A.measure :=
    (D.model_integrable N).norm.add D.boundary_integrable
  have hbasis : Integrable
      (CompletedAdelicPointHeights.logNorm B m F (F.basis ())) A.measure :=
    Integrable.mono' hbound hmeas hdom
  have ha : F.basis.repr e () ≠ 0 := by
    intro h
    apply he
    rw [MeasuredLinePointHeights.basis_scalar A X L F e, h, zero_smul]
  have heq : e = (F.basis.repr e ()) • F.basis () :=
    MeasuredLinePointHeights.basis_scalar A X L F e
  rw [heq]
  have hdecomp :
      CompletedAdelicPointHeights.logNorm B m F ((F.basis.repr e ()) • F.basis ()) =
        (fun v ↦ Real.log ‖A.embedding v (F.basis.repr e ())‖) +
          CompletedAdelicPointHeights.logNorm B m F (F.basis ()) := by
    funext v
    exact CompletedAdelicPointHeights.logNorm_smul B m F _ ha _ (F.basis.ne_zero ()) v
  rw [hdecomp]
  exact (A.integrable _ ha).add hbasis

end WantedExt.AlgebraicGeometry.CompletedAdelicPointHeights
