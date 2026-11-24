/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AdelicCompletionEvaluations
public import MathlibExt.AlgebraicGeometry.MetrizedLineOperationModels

/-!
# Operations on the same completed adelic metric

All results are rational-model classes in the original boundary Cauchy
quotient. Tensor, dual, power and pullback norms are fixed on actual
completed fibres and local-section germs. Pullback retains the literal
base-changed scheme map, native line comparison, residue-field map and
the boundary domination needed to preserve Cauchy convergence.

These are source-normalized construction endpoints; their producers
belong in the direct Wanted module.
Modelled on Yuan--Zhang, arXiv:2105.13587v9, Sections 2.5--2.6 and 3.4.
The completion is the fixed-gauge completion of `BoundaryMetricCompletionModels`, not
Yuan--Zhang's boundary topology: their adelic line bundles and positivity notions are not
claimed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AdelicCompletionOperations

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open CoherentCurveLinearSeries PlacewiseMetrizedLineModels BoundaryMetricCompletionModels
open RationalAdelicModelMetrics AdelicCompletionEvaluations MetrizedFibrePowerModels
open scoped TensorProduct

variable {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}
  {L M : X.left.Modules} (B : EffectiveBoundary A X)

/-- The actual global tensor sheaf, normalized on every pulled-back algebraic section. -/
structure AllPlaceTensor where
  map : ∀ (v : A.places) (p : Point (A := A) (X := X) v),
    Vector (L := L) v p ⊗[ValuedLineFibres.CompletedResidue _ _ p] Vector (L := M) v p ≃ₗ[
      ValuedLineFibres.CompletedResidue _ _ p]
        Vector (L := CurvePositivity.moduleTensor X.left L M) v p
  normalized : ∀ (U : X.left.Opens) (s : Γ(L,U)) (t : Γ(M,U)) (v : A.places)
    (p : Point (A := A) (X := X) v) (hp : placeProjection A X v p.schemePoint ∈ U),
    map v p ((ValuedLineFibres.evaluateSection _ _ _ (placeSection U s v) p hp) ⊗ₜ
      (ValuedLineFibres.evaluateSection _ _ _ (placeSection U t v) p hp)) =
      ValuedLineFibres.evaluateSection _ _ _ (placeSection U (tensorSectionAt L M U s t) v) p hp

/-- Completed isometries retain the original algebraic line isomorphism and germs. -/
structure AllPlaceIso (e : L ≅ M) where
  map : ∀ (v : A.places) (p : Point (A := A) (X := X) v),
    Vector (L := L) v p ≃ₗ[ValuedLineFibres.CompletedResidue _ _ p] Vector (L := M) v p
  normalized : ∀ (U : X.left.Opens) (s : Γ(L,U)) (v : A.places)
    (p : Point (A := A) (X := X) v) (hp : placeProjection A X v p.schemePoint ∈ U),
    map v p (ValuedLineFibres.evaluateSection _ _ _ (placeSection U s v) p hp) =
      ValuedLineFibres.evaluateSection _ _ _ (placeSection U (e.hom.app U s) v) p hp

def IsIsometric (m : FixedGaugeAdelicMetric (L := L) B) (n : FixedGaugeAdelicMetric (L := M) B) :
    Prop :=
  ∃ (e : L ≅ M) (F : AllPlaceIso (A := A) (X := X) e),
    ∀ v p z, fibreNorm B n.val v p (F.map v p z) = fibreNorm B m.val v p z

structure TensorResult (F : AllPlaceTensor (A := A) (X := X) (L := L) (M := M))
    (m : FixedGaugeAdelicMetric (L := L) B) (n : FixedGaugeAdelicMetric (L := M) B) where
  metric : FixedGaugeAdelicMetric (L := CurvePositivity.moduleTensor X.left L M) B
  normalized : ∀ v p z w, fibreNorm B metric.val v p (F.map v p (z ⊗ₜ w)) =
    fibreNorm B m.val v p z * fibreNorm B n.val v p w

structure PowerResult (m : FixedGaugeAdelicMetric (L := L) B) (r : ℕ)
    (F : AllPlacePower (A := A) (X := X) (L := L) r) where
  metric : FixedGaugeAdelicMetric (L := CurvePositivity.power L r) B
  normalized : ∀ v p z, fibreNorm B metric.val v p (F.map v p z) =
    fibreNorm B m.val v p z ^ r

/-- The global algebraic dual is characterized by its actual full sheaf-Hom evaluation:
`MetrizedLineOperationModels.DualLine`. -/
abbrev AlgebraicDual := MetrizedLineOperationModels.DualLine K X L

structure AllPlaceDual (D : AlgebraicDual (X := X) (L := L)) where
  map : ∀ (v : A.places) (p : Point (A := A) (X := X) v), Vector (L := D.line) v p ≃ₗ[
    ValuedLineFibres.CompletedResidue _ _ p]
      Module.Dual (ValuedLineFibres.CompletedResidue _ _ p) (Vector (L := L) v p)
  normalized : ∀ (U : X.left.Opens) (s : Γ(L,U)) (t : Γ(D.line,U)) (v : A.places)
    (p : Point (A := A) (X := X) v) (hp : placeProjection A X v p.schemePoint ∈ U),
    map v p (ValuedLineFibres.evaluateSection _ _ _ (placeSection U t v) p hp)
      (ValuedLineFibres.evaluateSection _ _ _ (placeSection U s v) p hp) =
        ValuedLineFibres.completionUnit _ _ p
          ((placeScheme A X v).left.evaluation _ p.schemePoint hp
            ((placeProjection A X v).app U (D.evaluation.app U (tensorSectionAt L D.line U s t))))

structure DualResult (m : FixedGaugeAdelicMetric (L := L) B) (D : AlgebraicDual (X := X) (L := L))
    (F : AllPlaceDual (A := A) D) where
  metric : FixedGaugeAdelicMetric (L := D.line) B
  normalized : ∀ v p z w, w ≠ 0 → fibreNorm B metric.val v p z =
    ‖F.map v p z w‖ / fibreNorm B m.val v p w

variable {Y : Over (Spec (.of K))} (f : Y ⟶ X)

def placeMap (v : A.places) : placeScheme A Y v ⟶ placeScheme A X v :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (A.embedding v)))).map f

theorem placeMap_projection (v : A.places) :
    (placeMap f v).left ≫ placeProjection A X v = placeProjection A Y v ≫ f.left := by
  simp [placeMap, placeProjection, Over.pullback]

def placePullbackLine (v : A.places) :
    (Scheme.Modules.pullback (placeMap f v).left).obj (placeLine A X L v) ≅
      placeLine A Y ((Scheme.Modules.pullback f.left).obj L) v :=
  (Scheme.Modules.pullbackComp (placeMap f v).left (placeProjection A X v)).app L ≪≫
    eqToIso (congrArg (fun g ↦ (Scheme.Modules.pullback g).obj L) (placeMap_projection f v)) ≪≫
    ((Scheme.Modules.pullbackComp (placeProjection A Y v) f.left).app L).symm

structure AllPlacePullback where
  fibre : ∀ v : A.places, MetrizedLineOperationModels.PullbackFibre (A.completion v)
    (placeScheme A X v) (placeLine A X L v) (placeMap f v)
  lineFibre : ∀ v : A.places, MetrizedLineOperationModels.FibreIso (A.completion v)
    (placeScheme A Y v) ((Scheme.Modules.pullback (placeMap f v).left).obj (placeLine A X L v))
    (placeLine A Y ((Scheme.Modules.pullback f.left).obj L) v) (placePullbackLine (L := L) f v)

def BoundaryDominated (C : EffectiveBoundary A Y) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ (v : A.places)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A Y v)),
    gauge A X B.toBoundary v (MetrizedLineOperationModels.mapPoint _ _ (placeMap f v) p) ≤
      c * gauge A Y C.toBoundary v p

structure PullbackResult (C : EffectiveBoundary A Y) (m : FixedGaugeAdelicMetric (L := L) B)
    (F : AllPlacePullback (A := A) (L := L) f) where
  metric : FixedGaugeAdelicMetric (L := (Scheme.Modules.pullback f.left).obj L) C
  normalized : ∀ (v : A.places)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A Y v))
    (a : ValuedLineFibres.CompletedResidue _ _ p)
    (z : Vector (L := L) v (MetrizedLineOperationModels.mapPoint _ _ (placeMap f v) p)),
    letI := ((F.fibre v).embedding p).toAlgebra
    fibreNorm C metric.val v p ((F.lineFibre v).map p ((F.fibre v).comparison p (a ⊗ₜ z))) =
      ‖a‖ * fibreNorm B m.val v (MetrizedLineOperationModels.mapPoint _ _ (placeMap f v) p) z

end MathlibExt.AlgebraicGeometry.AdelicCompletionOperations
