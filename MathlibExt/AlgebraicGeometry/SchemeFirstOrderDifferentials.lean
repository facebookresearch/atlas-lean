/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MarkedHomEvaluationDifferentials
public import MathlibExt.AlgebraicGeometry.StableMapCompositionFamilies
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Actual dual-number point classes and parameter differentials

The first-order point is an actual Spec(Ω⊕Ω) map with its exact
reduction. Its differential on every local function is the literal
square-zero coefficient. The cotangent projection is fixed on each
actual polynomial-resolution generator; H0 comparisons use the native
derived pullback counit. The resulting derived class is computed from
these maps, not selected by a pointed-set equivalence.

These operations supply the parameter-chart differential for stable-map
composition, forgetting/stabilization, and the Hurwitz branch map.
References: Behrend–Fantechi alg-geom/9601010v1, §§4/6;
Graber–Harris–Starr math/0109220v1, §2; Stacks, Tags 08S3/08UX.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SchemeFirstOrderDifferentials

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicTopology _root_.Simplicial
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.GenericSectionMaps
open MathlibExt.AlgebraicGeometry.GeometricCotangentComplex
open MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory
open MathlibExt.AlgebraicGeometry.MarkedMapDeformationCones
open MathlibExt.AlgebraicGeometry.MarkedFirstOrderFamilies
open MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves
open MathlibExt.AlgebraicGeometry.LocalDifferentialPullbacks
open MathlibExt.AlgebraicGeometry.RelativeReflexiveCanonicalPowers
open MathlibExt.AlgebraicGeometry.ModuleDerivedSquares
attribute [local instance] HasDerivedCategory.standard
open scoped Simplicial

variable {k : Type} [CommRing k]

/-- The actual relative cotangent projection to Kähler one-forms. -/
structure CotangentFormsProjection (U : Over (Spec (.of k)))
    (P : CotangentNormalization U.hom) where
  map : P.complex ⟶ (CochainComplex.singleFunctor U.left.Modules 0).obj (forms k U 1)
  normalized : ∀ (a : AffineChart U.hom)
    (x : (P.resolution a).algebra.obj (op ⦋0⦌)),
    (((map.f 0) ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (forms k U 1)).hom).app a.source)
      (((P.comparison a).f 0)
        ((affineDegreeIso (P.resolution a) 0).inv
          (CommAlgCat.resolutionCotangentTermDifferential a.base (CommAlgCat.of a.base a.ring)
            (P.resolution a).algebra (P.resolution a).augmentation (op ⦋0⦌) x))) =
      differential U a.source ((P.resolution a).augmentation.app (op ⦋0⦌) x)

variable [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]

/-- H0 of the actual left-derived pullback maps to ordinary pullback through its native counit. -/
def pullbackH0Map {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules) :
    (DerivedCategory.homologyFunctor X.Modules 0).obj
      ((derivedPullback f).obj ((DerivedCategory.singleFunctor Y.Modules 0).obj M)) ⟶
        (Scheme.Modules.pullback f).obj M :=
  (DerivedCategory.homologyFunctor X.Modules 0).map
      ((derivedPullbackCounit f).app ((CochainComplex.singleFunctor Y.Modules 0).obj M) ≫
        DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.pullback f) (.up ℤ) 0).app M).hom) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).hom.app
      ((Scheme.Modules.pullback f).obj M)

structure PullbackH0 {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules) where
  comparison : (DerivedCategory.homologyFunctor X.Modules 0).obj
    ((derivedPullback f).obj ((DerivedCategory.singleFunctor Y.Modules 0).obj M)) ≅
      (Scheme.Modules.pullback f).obj M
  normalized : comparison.hom = pullbackH0Map f M

/-- The native H0 projection is fixed by its identity on H0 and the actual nonpositive bound. -/
structure H0Projection {X : Scheme.{0}} (K : D X) where
  [bounded : K.IsLE 0]
  map : K ⟶ (DerivedCategory.singleFunctor X.Modules 0).obj
    ((DerivedCategory.homologyFunctor X.Modules 0).obj K)
  normalized : (DerivedCategory.homologyFunctor X.Modules 0).map map ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).hom.app
      ((DerivedCategory.homologyFunctor X.Modules 0).obj K) = 𝟙 _

variable (U : Over (Spec (.of k))) (P : CotangentNormalization U.hom)
    {Ω : Type} [Field Ω] (p : Spec (.of Ω) ⟶ U.left)

abbrev pointCotangent : D (Spec (.of Ω)) :=
  (derivedPullback p).obj (DerivedCategory.Q.obj P.complex)

/-- The point comparison is fixed by the polynomial cotangent projection
and actual derived counit. -/
structure PointCotangentH0 (F : CotangentFormsProjection U P) where
  pullback : PullbackH0 p (forms k U 1)
  comparison : (DerivedCategory.homologyFunctor (Spec (.of Ω)).Modules 0).obj
    (pointCotangent U P p) ≅ (Scheme.Modules.pullback p).obj (forms k U 1)
  normalized : comparison.hom =
    (DerivedCategory.homologyFunctor (Spec (.of Ω)).Modules 0).map
      ((derivedPullback p).map (DerivedCategory.Q.map F.map)) ≫ pullback.comparison.hom

/-- Source normalization on every regular function uses the actual ε coefficient of its pullback. -/
structure PointDifferential {b : Spec (.of Ω) ⟶ Spec (.of k)} (hp : p ≫ U.hom = b)
    (D : PointDeformation p hp) where
  map : (Scheme.Modules.pullback p).obj (forms k U 1) ⟶ structureModule (Spec (.of Ω))
  normalized : ∀ (W : U.left.Opens) (h : (⊤ : (Spec (.of (DualNumbers Ω))).Opens) ≤ D.map ⁻¹ᵁ W)
    (h₀ : (⊤ : (Spec (.of Ω)).Opens) ≤ p ⁻¹ᵁ W) (a : Γ(U.left,W)),
    (Scheme.ΓSpecIso (.of Ω)).hom.hom
      ((map.app ⊤) (localPullbackSection p (forms k U 1) W ⊤ h₀ (differential U W a))) =
    TrivSqZeroExt.snd ((Scheme.ΓSpecIso (.of (DualNumbers Ω))).hom.hom
      ((D.map.appLE W ⊤ h).hom a))

/-- The actual derived deformation class is H0 projection followed by
this normalized differential. -/
def pointClass {F : CotangentFormsProjection U P} (H : PointCotangentH0 U P p F)
    (Q : H0Projection (pointCotangent U P p))
    {b : Spec (.of Ω) ⟶ Spec (.of k)} {hp : p ≫ U.hom = b}
    {D : PointDeformation p hp} (E : PointDifferential U p hp D) :
    pointCotangent U P p ⟶ derivedUnit (Spec (.of Ω)) :=
  Q.map ≫ (DerivedCategory.singleFunctor (Spec (.of Ω)).Modules 0).map (H.comparison.hom ≫ E.map)

/-- First-order chart composition is the literal composition of the two actual scheme maps. -/
def composePoint {V : Over (Spec (.of k))} (f : U ⟶ V)
    {b : Spec (.of Ω) ⟶ Spec (.of k)} {hp : p ≫ U.hom = b}
    (D : PointDeformation p hp) :
    PointDeformation (q := V.hom) (b := b) (p ≫ f.left)
      (by rw [Category.assoc, Over.w f, hp]) where
  map := D.map ≫ f.left
  over := by rw [Category.assoc, Over.w f, D.over]
  reduction_map := by rw [← Category.assoc, D.reduction_map]

/-- The point cotangent differential is the actual normalized global derivative
pulled back through the native composition comparison. -/
def pointCotangentMap {V : Over (Spec (.of k))} (f : U ⟶ V)
    (Q : CotangentNormalization V.hom)
    (D : RelativeDifferential f.left (Over.w f) P Q) (A : PullbackPasting p f.left) :
    pointCotangent V Q (p ≫ f.left) ⟶ pointCotangent U P p :=
  A.comparison.inv.app (DerivedCategory.Q.obj Q.complex) ≫ (derivedPullback p).map D.derived

/-- The differential on actual tangent classes is literal cotangent precomposition. -/
def mapPointClass {V : Over (Spec (.of k))} (f : U ⟶ V)
    (Q : CotangentNormalization V.hom)
    (D : RelativeDifferential f.left (Over.w f) P Q) (A : PullbackPasting p f.left)
    (ξ : pointCotangent U P p ⟶ derivedUnit (Spec (.of Ω))) :
    pointCotangent V Q (p ≫ f.left) ⟶ derivedUnit (Spec (.of Ω)) :=
  pointCotangentMap U P p f Q D A ≫ ξ

end MathlibExt.AlgebraicGeometry.SchemeFirstOrderDifferentials
