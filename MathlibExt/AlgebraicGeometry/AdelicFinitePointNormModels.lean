/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FiniteAdelicTensorFactors
public import MathlibExt.AlgebraicGeometry.FinitePointNormLines
public import MathlibExt.AlgebraicGeometry.AdelicPicardVectors
public import MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights

/-!
# Source-qualified finite-point norm metrics

Every place uses the whole `E tensor_K K_v` algebra and its actual local
Artinian factors. Its residue/completion fields retain the original scalar
maps. Scheme maps are literal pullback lifts of the original closed point.
Completed point-field dictionaries fix the entire map from `Spec W` and the
actual completion unit, not merely the point set.

A norm result uses the actual exterior determinant Hom line, the actual
finite-point fibre vectors and a paired source/target rational-model sequence.
Its norm at every model stage is the product of the actual source norms with
Artinian length times completed-field rank. The target boundary is part of
the constructed norm model. Vector heights then belong to the same full
Picard presentation, even when that boundary changes.

Modelled on Yuan--Zhang, arXiv:2105.13587v9, Sections 3.4 and 5.3.1.
No separability, independently supplied norm provider, or assigned height
function is an input to these construction requests.
The completion is the fixed-gauge completion of `BoundaryMetricCompletionModels`, not
Yuan--Zhang's boundary topology: their adelic line bundles and positivity notions are not
claimed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AdelicFinitePointNormModels

open CategoryTheory CategoryTheory.Limits Opposite Module
open _root_.AlgebraicGeometry
open CoherentCurveLinearSeries PlacewiseMetrizedLineModels BoundaryMetricCompletionModels
open RationalAdelicModelMetrics AdelicSemipositiveClosures
open FiniteAdelicTensorFactors FinitePointNormLines
open AdelicPicardVectors MeasuredLinePointHeights

variable {K E : Type} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
  (A : AdelicField K)

/-- The completed base scalar action is fixed by the original adelic embedding. -/
@[instance_reducible] def normPlaceAlgebra (v : A.places) : Algebra K (A.completion v) :=
  (A.embedding v).toAlgebra

attribute [local instance] normPlaceAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Complete local tensor factors and their literal scalar-base square. -/
structure PlaceFactors where
  factorization : ∀ v : A.places, Factorization K E (A.completion v)
  completions : ∀ v, CompletionData (factorization v)
  scalarSquare : ∀ (v : A.places) (i : (factorization v).index),
    Spec.map (CommRingCat.ofHom (completionMap (factorization v) (completions v) i)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K E)) =
      Spec.map (CommRingCat.ofHom (algebraMap (A.completion v) ((completions v).completion i))) ≫
        Spec.map (CommRingCat.ofHom (A.embedding v))

variable {A} (D : PlaceFactors (E := E) A)
  {X : Over (Spec (.of K))} (x : ClosedPoint (K := K) (E := E) X)

/-- The actual complete factor field, including its fixed source scalar maps. -/
abbrev FactorField (v : A.places) (i : (D.factorization v).index) :=
  (D.completions v).completion i

/-- The field-point map is the native base-change lift of the same original point. -/
def placePointMap (v : A.places) (i : (D.factorization v).index) :
    Spec (.of (FactorField D v i)) ⟶ (placeScheme A X v).left :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (completionMap (D.factorization v) (D.completions v) i)) ≫
      x.map.left)
    (Spec.map (CommRingCat.ofHom (algebraMap (A.completion v) (FactorField D v i))))
    (by rw [Category.assoc, x.map.w]; exact D.scalarSquare v i)

/-- Pull an actual line section into this same algebraic finite-point fibre. -/
def pointSection (L : X.left.Modules) (U : X.left.Opens) (s : Γ(L,U))
    (hx : x.map.left (IsLocalRing.closedPoint E) ∈ U) : pointFibre L x.map :=
  GenericSectionMaps.localPullbackSection x.map.left L U ⊤ (by
    let : Subsingleton (fieldPoint (K := K) (E := E)).left :=
      inferInstanceAs (Subsingleton (Spec (.of E)))
    intro y _hy
    change x.map.left y ∈ U
    rw [show y = IsLocalRing.closedPoint E from Subsingleton.elim _ _]
    exact hx) s

variable (L : X.left.Modules)

/-- The completed residue dictionary and fibre vectors are fixed on actual scheme maps. -/
structure PointRealization (v : A.places) (i : (D.factorization v).index) where
  point : ValuedLineFibres.Point (A.completion v) (placeScheme A X v)
  residue : (placeScheme A X v).left.residueField point.schemePoint ≃+* FactorField D v i
  sourceMap : Spec.map (CommRingCat.ofHom residue.toRingHom) ≫
    (placeScheme A X v).left.fromSpecResidueField point.schemePoint = placePointMap D x v i
  normSource : ∀ a, point.absoluteValue a = ‖residue a‖
  completion : ValuedLineFibres.CompletedResidue (A.completion v) (placeScheme A X v) point ≃+*
    FactorField D v i
  completionUnit : ∀ a, completion (ValuedLineFibres.completionUnit _ _ point a) = residue a
  completionNorm : ∀ a, ‖completion a‖ = ‖a‖
  schemeNormalized : placeProjection A X v point.schemePoint =
    x.map.left (IsLocalRing.closedPoint E)
  vector : pointFibre L x.map →ₛₗ[
    completion.symm.toRingHom.comp
      (completionMap (D.factorization v) (D.completions v) i)]
    ValuedLineFibres.Fibre (A.completion v) (placeScheme A X v) (placeLine A X L v) point
  injective : Function.Injective vector
  sections : ∀ (U : X.left.Opens) (s : Γ(L,U))
    (hx : x.map.left (IsLocalRing.closedPoint E) ∈ U),
    vector (pointSection x L U s hx) =
      ValuedLineFibres.evaluateSection _ _ _ (RationalAdelicModelMetrics.placeSection U s v)
        point (by change placeProjection A X v point.schemePoint ∈ U
                  rw [schemeNormalized]
                  exact hx)

variable (G : GroundBase (K := K)) (M : LineObject (A := A) (X := X) G)
  (b : Basis Unit E (pointFibre M.line x.map))

/-- A source/target paired norm model on the actual exterior determinant Hom line. -/
structure NormResult where
  boundary : EffectiveBoundary A (BasePoint (K := K))
  isLine : IsLineBundle (normLine (K := K) (pointFibre M.line x.map))
  metric : FixedGaugeAdelicMetric (L := normLine (K := K) (pointFibre M.line x.map)) boundary
  integrable : IsIntegrable G boundary metric
  frame : PointFrame A (BasePoint (K := K))
    (normLine (K := K) (pointFibre M.line x.map)) (𝟙 (BasePoint (K := K)))
  affine : normModule (K := K) (pointFibre M.line x.map) ≃ₗ[K]
    AlgebraicFibre (BasePoint (K := K)) (normLine (K := K) (pointFibre M.line x.map))
      (𝟙 (BasePoint (K := K)))
  sourceSequence : ModelSequence (L := M.line) M.boundary
  sourceClass : sourceSequence.class = M.metric.val
  targetSequence : ModelSequence (L := normLine (K := K) (pointFibre M.line x.map)) boundary
  targetClass : targetSequence.class = metric.val
  realization : ∀ (v : A.places) (i : (D.factorization v).index), PointRealization D x M.line v i
  sourceDense : ∀ n, DenseRange (sourceSequence.model n).integral.model.openMap.left
  targetDense : ∀ n, DenseRange (targetSequence.model n).integral.model.openMap.left
  modelNorm : ∀ (n : ℕ) (v : A.places) (u : pointFibre M.line x.map), u ≠ 0 →
    norm (targetSequence.model n).metric v (frame.point v)
        (frame.vector v (affine (normElement (K := K) (pointFibre M.line x.map) b u))) =
      ∏ i : (D.factorization v).index,
        norm (sourceSequence.model n).metric v (realization v i).point
          ((realization v i).vector u) ^ completionWeight (D.factorization v) (D.completions v) i

variable (N : NormResult D x G M b)

/-- The norm is one actual integrable adelic line object in the full field Picard presentation. -/
def NormResult.asObject : LineObject (A := A) (X := BasePoint (K := K)) G :=
  ⟨normLine (K := K) (pointFibre M.line x.map), N.isLine, N.boundary, N.metric, N.integrable⟩

/-- Section5.3.1 normalization uses the actual finite residue-field degree. -/
def vectorHeight : PicardVector (A := A) (X := BasePoint (K := K)) (G := G) :=
  (Module.finrank K E : ℚ)⁻¹ • lineClass N.asObject

end MathlibExt.AlgebraicGeometry.AdelicFinitePointNormModels
