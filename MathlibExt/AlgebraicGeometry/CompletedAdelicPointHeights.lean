/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AdelicCompletionEvaluations
public import MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights

/-!
# Point heights of the actual completed adelic metric

Height integrates the already computed logarithmic evaluation of the
original Cauchy quotient. Scalar independence uses that quotient's
proved scalar formula and the original place measure. The approximation
condition retains a genuine rational-model representative and an
integrable boundary gauge; interchange of the integral and limit is a
separate construction request.
Modelled on Yuan--Zhang, arXiv:2105.13587v9, Sections 3.4 and 5.3.
The completion is the fixed-gauge completion of `BoundaryMetricCompletionModels`, not
Yuan--Zhang's boundary topology: their adelic line bundles and positivity notions are not
claimed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights

open CategoryTheory _root_.AlgebraicGeometry MeasureTheory Filter
open PlacewiseMetrizedLineModels BoundaryMetricCompletionModels
open MeasuredLinePointHeights
open scoped Topology

variable {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}
  {L : X.left.Modules} (B : EffectiveBoundary A X)
  (m : BoundaryMetricCompletion (L := L) B)
  {x : BasePoint (K := K) ⟶ X} (F : PointFrame A X L x)

def logNorm (e : AlgebraicFibre X L x) : A.places → ℝ :=
  fun v ↦ AdelicCompletionEvaluations.logNorm B m v (F.point v) (F.vector v e)

def height (e : AlgebraicFibre X L x) : ℝ := -∫ v, logNorm B m F e v ∂A.measure

def IsAdmissible : Prop := ∀ e : AlgebraicFibre X L x, e ≠ 0 →
  Integrable (logNorm B m F e) A.measure

theorem logNorm_smul (a : K) (ha : a ≠ 0) (e : AlgebraicFibre X L x) (he : e ≠ 0)
    (v : A.places) :
    logNorm B m F (a • e) v = Real.log ‖A.embedding v a‖ + logNorm B m F e v := by
  unfold logNorm
  rw [F.vector v |>.map_smulₛₗ]
  have hv : completedScalars A X v (F.point v) a ≠ 0 := by
    simpa only [map_zero] using
      (RingHom.injective (completedScalars A X v (F.point v))).ne ha
  have he' : F.vector v e ≠ 0 := by
    intro h
    apply he
    apply F.injective v
    simpa only [map_zero] using h
  rw [AdelicCompletionEvaluations.logNorm_smul B m v (F.point v) _ hv _ he',
    completedScalars_norm]

theorem height_smul (H : IsAdmissible B m F) (a : K) (ha : a ≠ 0)
    (e : AlgebraicFibre X L x) (he : e ≠ 0) :
    height B m F (a • e) = height B m F e := by
  have h : logNorm B m F (a • e) =
      (fun v ↦ Real.log ‖A.embedding v a‖) + logNorm B m F e := by
    funext v
    exact logNorm_smul B m F a ha e he v
  simp only [height, h, Pi.add_apply]
  rw [integral_add (A.integrable a ha) (H e he), A.product_formula a ha, zero_add]

theorem height_independent (H : IsAdmissible B m F)
    (e f : AlgebraicFibre X L x) (he : e ≠ 0) (hf : f ≠ 0) :
    height B m F e = height B m F f := by
  have hc (u : AlgebraicFibre X L x) (hu : u ≠ 0) : F.basis.repr u () ≠ 0 := by
    intro h
    apply hu
    rw [MeasuredLinePointHeights.basis_scalar A X L F u, h, zero_smul]
  rw [MeasuredLinePointHeights.basis_scalar A X L F e,
    MeasuredLinePointHeights.basis_scalar A X L F f]
  rw [height_smul B m F H _ (hc e he) _ (F.basis.ne_zero ()),
    height_smul B m F H _ (hc f hf) _ (F.basis.ne_zero ())]

/-- This height consumes the original Cauchy class, not a separately supplied metric, and is
defined for admissible classes. `height` itself is the raw integral, which is zero by convention
when the log norm is not integrable. -/
def pointHeight (_H : IsAdmissible B m F) : ℝ := height B m F (F.basis ())

def adelicPointHeight (m : RationalAdelicModelMetrics.FixedGaugeAdelicMetric (L := L) B)
    (H : IsAdmissible B m.val F) : ℝ :=
  pointHeight B m.val F H

/-- The constant metric embeds with its original point-height normalization. -/
theorem pointHeight_constant (N : MetrizedLine A X L)
    (H : IsAdmissible B (AdelicCompletionEvaluations.constantClass B N) F)
    (H' : MeasuredLinePointHeights.IsAdmissible A X L N F) :
    pointHeight B (AdelicCompletionEvaluations.constantClass B N) F H =
      MeasuredLinePointHeights.pointHeight A X L N F H' := by
  unfold pointHeight height MeasuredLinePointHeights.pointHeight MeasuredLinePointHeights.height
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  exact AdelicCompletionEvaluations.logNorm_constant B N v (F.point v) (F.vector v (F.basis ()))

/-- Actual model approximation and the boundary domination needed for measured heights. -/
structure DominatedApproximation where
  sequence : RationalAdelicModelMetrics.ModelSequence (L := L) B
  class_normalized : sequence.class = m
  model_integrable : ∀ n, Integrable
    (MeasuredLinePointHeights.logNorm A X L (sequence.model n).metric F (F.basis ())) A.measure
  boundary_integrable : Integrable
    (fun v ↦ gauge A X B.toBoundary v (F.point v)) A.measure

/-- The limit statement is about the actual model heights and the computed quotient height,
as integrals of the basis vector's log norms; `D` records their integrability. -/
def HeightConverges (D : DominatedApproximation B m F) : Prop :=
  Tendsto (fun n ↦ MeasuredLinePointHeights.height A X L (D.sequence.model n).metric F (F.basis ()))
    atTop (𝓝 (height B m F (F.basis ())))

end MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights
