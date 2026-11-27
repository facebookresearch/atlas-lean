/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies
public import MathlibExt.AlgebraicGeometry.NativeLargeModuleLifts
public import MathlibExt.AlgebraicGeometry.GeometricPerfectDGYonedaModels

/-!
# Native full-enveloping geometric moduli points and their RHom span

The tests are the literal augmented DG-frame objects of the source small
perfect model. Their geometric functor is normalized on every original
object and homogeneous cochain. Native derived inverse image of this
whole test diagram is used on each actual coefficient family X_A.

The geometric enveloping-module realization is fixed by every actual
test Hom complex, source precomposition, coefficient action and target
postcomposition. A moduli point is represented by a weak map between
actual cofibrant modules over that full enveloping category. The RHom
comparison is the span of the original lift, projective-module and
native geometric augmentation maps. No geometric RHom identification
or tangent conclusion is a field of an independent source input.

References: Toen--Vaquie math/0503269v5, Sections3.1/3.3/3.5; Stacks
03G8,06YY,0DLD/0DLE. The original full DG-module, cochain and native
small-etale source credits remain in the imported modules.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ProperGeometricModuliRHomModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
open MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations
open MathlibExt.AlgebraicGeometry.SpaceGeometricDGHomSources
open MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies
open MathlibExt.AlgebraicGeometry.GeometricPerfectTestModels
open MathlibExt.AlgebraicGeometry.GeometricPerfectDGYonedaModels
open MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies
open MathlibExt.AlgebraicGeometry.NativeLargeModuleLifts
open CochainComplex.HomComplex
open scoped Simplicial

universe u

attribute [local instance] HasDerivedCategory.standard

variable (O : ∀ Z : Scheme.{u}, EtaleStructureSource Z) [SourceTheory.{u}]
  (L : EtalePullbackSystem O)
  (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A)
  (C : ChartRestrictionSystem O)
  (D : ProperSpaceSituation.{u}) (B : AffineProperFamily D)
  (SB : ScalarLinearitySource B.ring (affineProperProjection D B))
  (UL : CochainLiftModel B.ring)
  (T : SmallPerfectTestModel O L J C SB UL)
  (F : DGFrame B.ring (oppositeCategory T.category))

/-- The original zero-frame perfect tests with the fixed native coefficient-universe lift. -/
def frameTestCategory {k : Type u} [CommRing k] (UL : CochainLiftModel k)
    {T₀ : DGCat k} (F : DGFrame k (oppositeCategory T₀)) : DGCat (LargeScalar k) :=
  liftedDGCategory UL (oppositeCategory (F.diagram.obj ⦋0⦌))

/-- Every actual source-frame test and cochain is fixed by the original DG augmentation and perfect realization. -/
structure NativeFramePerfectTests where
  functor : EnrichedFunctor (Cochains (LargeScalar B.ring))
    (frameTestCategory UL F) (geometricDG SB)
  object_eq : ∀ r : F.diagram.obj ⦋0⦌,
    functor.obj (ULift.up (op r)) =
      (T.realization.obj (ULift.up (((F.augmentation.app ⦋0⦌).obj r).unop))).obj
  hom_eq : ∀ (r r' : F.diagram.obj ⦋0⦌) (n : ℤ) (a : DGHom B.ring n r r'),
    HEq (functor.dgMap n (X := ULift.up (op r')) (Y := ULift.up (op r)) (ULift.up a))
      (T.realization.dgMap n
        (X := ULift.up (((F.augmentation.app ⦋0⦌).obj r').unop))
        (Y := ULift.up (((F.augmentation.app ⦋0⦌).obj r).unop))
        (ULift.up ((F.augmentation.app ⦋0⦌).dgMap n a)))

variable {N : ShuffleAlgebraFunctor B.ring} {S : AffineScalarSystem N}
  (P : StrictPerfectSystem N S) (A : CommAlgCat.{u} B.ring)

/-- The point's original complete T-action and coefficient action live in this actual enveloping category. -/
def ordinaryEnvelope {k : Type u} [CommRing k] {T₀ : DGCat k}
    (F : DGFrame k (oppositeCategory T₀)) (N : ShuffleAlgebraFunctor k)
    (A : CommAlgCat.{u} k) : DGCat k :=
  enveloping (F.diagram.obj ⦋0⦌) (coefficientCategory N (ordinaryAlgebras.obj A))

/-- The original whole enveloping category, with only the native coefficient universe changed. -/
def largeOrdinaryEnvelope {k : Type u} [CommRing k] (UL : CochainLiftModel k) {T₀ : DGCat k}
    (F : DGFrame k (oppositeCategory T₀)) (N : ShuffleAlgebraFunctor k)
    (A : CommAlgCat.{u} k) : DGCat (LargeScalar k) :=
  liftedDGCategory UL (ordinaryEnvelope F N A)

/-- The actual coefficient-unit test of this full enveloping module. -/
def envelopeTest {k : Type u} [CommRing k] (UL : CochainLiftModel k) {T₀ : DGCat k}
    (F : DGFrame k (oppositeCategory T₀)) (N : ShuffleAlgebraFunctor k)
    (A : CommAlgCat.{u} k) (r : F.diagram.obj ⦋0⦌) : (largeOrdinaryEnvelope UL F N A)ᵒᵖ :=
  op (ULift.up (op r, PUnit.unit))

/-- An original homogeneous test cochain is the actual pure-tensor generator with the coefficient identity. -/
def testGenerator {k : Type u} [CommRing k] (UL : CochainLiftModel k) {T₀ : DGCat k}
    (F : DGFrame k (oppositeCategory T₀)) (N : ShuffleAlgebraFunctor k) (A : CommAlgCat.{u} k)
    {r r' : F.diagram.obj ⦋0⦌} {n : ℤ} (a : DGHom k n r r') :
    DGHom (LargeScalar k) n (envelopeTest UL F N A r) (envelopeTest UL F N A r') :=
  ULift.up (tensorArrow (C := F.diagram.obj ⦋0⦌)
    (D := coefficientCategory N (ordinaryAlgebras.obj A)) a
    (dgId k (C := (coefficientCategory N (ordinaryAlgebras.obj A))ᵒᵖ)
      (op (PUnit.unit : coefficientCategory N (ordinaryAlgebras.obj A)))) (add_zero n))

/-- The actual ordinary coefficient a is the native degree-zero N(const A) action tensor the source identity. -/
def scalarTestGenerator {k : Type u} [CommRing k] (UL : CochainLiftModel k) {T₀ : DGCat k}
    (F : DGFrame k (oppositeCategory T₀)) (N : ShuffleAlgebraFunctor k) (A : CommAlgCat.{u} k)
    (K : OrdinaryCoefficientSource N A) (r : F.diagram.obj ⦋0⦌) (a : A) :
    DGHom (LargeScalar k) 0 (envelopeTest UL F N A r) (envelopeTest UL F N A r) :=
  ULift.up (tensorArrow (C := F.diagram.obj ⦋0⦌)
    (D := coefficientCategory N (ordinaryAlgebras.obj A)) (dgId k r)
    (K.degreeZero.symm a) (zero_add 0))

variable (Q : PullbackSystem.{u}) (FB : NativeFramePerfectTests O L J C D B SB UL T F)
  (SA : ScalarLinearitySource B.ring (baseCoefficientProjection D B A))
  (R : RawPullbackDGSource Q (coefficientSourceMap D B A) B.ring
    (affineProperProjection D B) (baseCoefficientProjection D B A) SB SA)
  (V : TestPullbackDGSource R (frameTestCategory UL F) FB.functor)

/-- This particular native geometric perfect test is the same target of the whole actual derived-pullback diagram. -/
def geometricTest (r : F.diagram.obj ⦋0⦌) : geometricDG SA :=
  V.target.obj (ULift.up (op r))

/-- The geometric enveloping functor is normalized on every source test and every target Hom component. -/
structure GeometricEnvelopingYoneda where
  coefficient : OrdinaryCoefficientSource N A
  functor : EnrichedFunctor (Cochains (LargeScalar B.ring)) (qcohDGCategory O L J C SA)
    (RightModule (LargeScalar B.ring) (largeOrdinaryEnvelope UL F N A))
  value_eq : ∀ (E : qcohDGCategory O L J C SA) (r : F.diagram.obj ⦋0⦌),
    (functor.obj E).toEnrichedFunctor.obj (envelopeTest UL F N A r) =
      dgHomComplex (LargeScalar B.ring) (geometricTest O L J C D B SB UL T F A Q FB SA R V r) E.obj
  test_action : ∀ (E : qcohDGCategory O L J C SA)
    (r r' : F.diagram.obj ⦋0⦌) (n : ℤ) (a : DGHom B.ring n r r'),
    HEq ((functor.obj E).toEnrichedFunctor.dgMap n (testGenerator UL F N A a))
      ((dgRepresentable (LargeScalar B.ring) E.obj).dgMap n
        (V.target.dgMap n (X := ULift.up (op r')) (Y := ULift.up (op r)) (ULift.up a)))
  scalar_action : ∀ (E : qcohDGCategory O L J C SA) (r : F.diagram.obj ⦋0⦌)
    (a : A) (i : ℤ)
    (x : ((functor.obj E).toEnrichedFunctor.obj (envelopeTest UL F N A r)).X i),
    let z := ((eqToHom (value_eq E r)).f i).hom x
    let az := ((eqToHom (value_eq E r)).f i).hom
      (cochainEval (LargeScalar B.ring) x 0 i (add_zero i)
        ((functor.obj E).toEnrichedFunctor.dgMap 0 (scalarTestGenerator UL F N A coefficient r a)))
    ∀ (j j' : ℤ) (h : j + i = j') (U : EtaleChart (coefficientSpace D B A))
      (s : ((geometricTest O L J C D B SB UL T F A Q FB SA R V r).X j).val.obj (op U)),
      (((az : Cochain (geometricTest O L J C D B SB UL T F A Q FB SA R V r) E.obj i).v j j' h).val.app (op U)).hom s =
        (chartScalarMap (ordinaryRing A) (coefficientProjection D B A) U a) •
          (((z : Cochain (geometricTest O L J C D B SB UL T F A Q FB SA R V r) E.obj i).v j j' h).val.app (op U)).hom s
  hom_normalized : ∀ (E E' : qcohDGCategory O L J C SA) (n : ℤ)
    (a : DGHom (LargeScalar B.ring) n E E') (r : F.diagram.obj ⦋0⦌),
    HEq (DGFunctor.dgApp (LargeScalar B.ring) n (envelopeTest UL F N A r)
      (functor.dgMap n a))
      (dgPostcomp (LargeScalar B.ring) (op (geometricTest O L J C D B SB UL T F A Q FB SA R V r)) n a)

section Replacement

variable {k : Type u} [CommRing k] (E : DGCat (LargeScalar k)) (W : DGCat (LargeScalar k))
  (Y : EnrichedFunctor (Cochains (LargeScalar k)) E (RightModule (LargeScalar k) W))
  (I : CofibrantReplacement E)

/-- One projective replacement of the same whole actual enriched module functor. -/
structure EnrichedModuleReplacementDiagram where
  functor : EnrichedFunctor (Cochains (LargeScalar k)) I.category (DGDerivedModules (LargeScalar k) W)
  augmentation : DGNatTrans
    (functor.comp (Cochains (LargeScalar k)) (cofibrantModulesToRaw (A := CommRingCat.of k) W))
    (I.augmentation.comp (Cochains (LargeScalar k)) Y)
  trivial : ∀ e : I.category, IsModuleTrivialFibration
    ((DGFunctor.homEquivDGCycles (LargeScalar k) (functor.obj e).obj (Y.obj (I.augmentation.obj e))).symm
      ⟨augmentation.dgApp e, augmentation.dgApp_mem_dgCycles e⟩)

end Replacement

variable {E : ((underivedModuliFunctor F P).obj A) _⦋0⦌}
  (M : ModulePointModel F P (ordinaryAlgebras.obj A) E)
  (ML : LargeProjectiveModuleLift UL (ordinaryEnvelope F N A) M.replacement.module)
  (Y : GeometricEnvelopingYoneda O L J C D B SB UL T F A Q FB SA R V)
  (I : CofibrantReplacement (qcohDGCategory O L J C SA))
  (Z : EnrichedModuleReplacementDiagram (qcohDGCategory O L J C SA)
    (largeOrdinaryEnvelope UL F N A) Y.functor I)

/-- The source point is an actual geometric cochain and a weak comparison over the full original T/coefficient action. -/
structure GeometricModuliPoint where
  index : I.category
  comparison : ML.module.obj ⟶ (Z.functor.obj index).obj
  weak : ∀ x : (largeOrdinaryEnvelope UL F N A)ᵒᵖ,
    QuasiIso (moduleComponent comparison x)

variable (G : GeometricModuliPoint O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z)

/-- The geometric object is the literal native source DG augmentation at the constructed point index. -/
def pointGeometry : qcohDGCategory O L J C SA := I.augmentation.obj G.index

/-- Its actual geometric endomorphisms are native all-degree Hom of that same small-etale cochain. -/
def pointGeometricEndomorphisms : Cochains (LargeScalar B.ring) :=
  dgHomComplex (LargeScalar B.ring) (pointGeometry O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G).obj
    (pointGeometry O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G).obj

/-- The actual common projective-module comparison cycle. -/
def pointComparisonCycle :
    DGHom (LargeScalar B.ring) 0 ML.module.obj (Z.functor.obj G.index).obj :=
  ((DGFunctor.homEquivDGCycles (LargeScalar B.ring) _ _) G.comparison).val

/-- The comparison is the original closed module map, not a separately supplied homogeneous arrow. -/
theorem pointComparisonCycle_closed :
    pointComparisonCycle O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G ∈
      dgCycles (LargeScalar B.ring) ML.module.obj (Z.functor.obj G.index).obj :=
  ((DGFunctor.homEquivDGCycles (LargeScalar B.ring) _ _) G.comparison).property

/-- The common source of the two actual projective-module Hom legs. -/
def pointModuleHomSpan : Cochains (LargeScalar B.ring) :=
  dgHomComplex (LargeScalar B.ring) ML.module.obj (Z.functor.obj G.index).obj

/-- The original full-enveloping endomorphism complex changes only its coefficient universe. -/
def pointLiftHomLeg :
    (largeCochainLift B.ring).obj (derivedEndomorphisms M) ⟶
      dgHomComplex (LargeScalar B.ring) ML.module.obj ML.module.obj :=
  ML.endomorphismMap

/-- Native target postcomposition by the same full-action point comparison. -/
def pointModulePostHomLeg :
    dgHomComplex (LargeScalar B.ring) ML.module.obj ML.module.obj ⟶
      pointModuleHomSpan O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G :=
  eHomWhiskerLeft (Cochains (LargeScalar B.ring)) (ForgetEnrichment.of _ ML.module.obj)
    (dgClosedHomOf (LargeScalar B.ring)
      (pointComparisonCycle O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G)
      (pointComparisonCycle_closed O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G))

/-- Native source precomposition by that same point comparison, between actual cofibrant modules. -/
def pointModulePreHomLeg :
    dgHomComplex (LargeScalar B.ring) (Z.functor.obj G.index).obj (Z.functor.obj G.index).obj ⟶
      pointModuleHomSpan O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G :=
  eHomWhiskerRight (Cochains (LargeScalar B.ring))
    (dgClosedHomOf (LargeScalar B.ring)
      (pointComparisonCycle O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G)
      (pointComparisonCycle_closed O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G))
    (ForgetEnrichment.of _ (Z.functor.obj G.index).obj)

/-- The actual whole geometric projective-module diagram supplies this enriched Hom leg. -/
def pointGeometryModuleHomLeg :
    dgHomComplex (LargeScalar B.ring) G.index G.index ⟶
      dgHomComplex (LargeScalar B.ring) (Z.functor.obj G.index).obj (Z.functor.obj G.index).obj :=
  Z.functor.map G.index G.index

/-- The actual native geometric augmentation supplies the final Hom leg to the same X_A cochain. -/
def pointGeometryHomLeg :
    dgHomComplex (LargeScalar B.ring) G.index G.index ⟶
      pointGeometricEndomorphisms O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G :=
  I.augmentation.map G.index G.index

/-- The source geometric augmentation supplies a quasi-isomorphism in every actual cohomological degree. -/
theorem pointGeometryHomLeg_quasiIso :
    QuasiIso (pointGeometryHomLeg O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G) := by
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_isIso_homologyMap
    (pointGeometryHomLeg O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G) n).mpr
      (EnrichedFunctor.IsQuasiFullyFaithful.isIso_homologyMap
        (EnrichedFunctor.IsQuasiEquivalence.isQuasiFullyFaithful I.trivialFibration.2)
        G.index G.index n)

section DerivedComparison

variable [QuasiIso ML.endomorphismMap]
  [QuasiIso (pointModulePostHomLeg O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G)]
  [QuasiIso (pointModulePreHomLeg O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G)]
  [QuasiIso (pointGeometryModuleHomLeg O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G)]

/-- The actual derived RHom comparison is the composite of the five fixed source-normalized span legs. -/
def pointDerivedRHomIso :
    DerivedCategory.Q.obj ((largeCochainLift B.ring).obj (derivedEndomorphisms M)) ≅
      DerivedCategory.Q.obj
        (pointGeometricEndomorphisms O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G) := by
  letI := pointGeometryHomLeg_quasiIso O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G
  exact asIso (DerivedCategory.Q.map ML.endomorphismMap) ≪≫
    asIso (DerivedCategory.Q.map
      (pointModulePostHomLeg O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G)) ≪≫
    (asIso (DerivedCategory.Q.map
      (pointModulePreHomLeg O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G))).symm ≪≫
    (asIso (DerivedCategory.Q.map
      (pointGeometryModuleHomLeg O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G))).symm ≪≫
    asIso (DerivedCategory.Q.map
      (pointGeometryHomLeg O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G))

end DerivedComparison

end MathlibExt.AlgebraicGeometry.ProperGeometricModuliRHomModels
