/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DGFrameCoefficientUnits
public import MathlibExt.AlgebraicGeometry.ProperGeometricModuliRHomModels
public import MathlibExt.AlgebraicGeometry.ProperCoefficientFunctorMaps

/-!
# Full native module realization before ordinary complexes truncation

The source is the actual category of all projective modules over the
entire original frame/coefficient envelope. Its large enrichment is
the fixed native coefficient lift. A DG quasi-functor roof is compared
on every module index and every homogeneous map with the actual native
all-perfect-test geometric Yoneda functor. The ordinary derived functor
is normalized on that whole roof, not on isolated moduli vertices.

Both interval legs are the SAME original enriched induction unit,
then the same complete module realization. Proper-flat supplies only
the perfect-to-pseudo-perfect direction. Smoothness is a separate
native chart-map predicate for ordinary equivalence on the actual
relative-perfect/no-negative-fibre-Ext locus.

Source: Toën--Vaquié arXiv:math/0503269v5, Section 3.5 pp.59--61,
especially Remark 3.30(2); Stacks 0DLD/0DLE. Native notices remain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ProperOrdinaryModuleRealization

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies
open MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations
open MathlibExt.AlgebraicGeometry.SpaceGeometricDGHomSources
open MathlibExt.AlgebraicGeometry.GeometricPerfectTestModels
open MathlibExt.AlgebraicGeometry.GeometricPerfectDGYonedaModels
open MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies
open MathlibExt.AlgebraicGeometry.ProperGeometricModuliRHomModels
open MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
open MathlibExt.AlgebraicGeometry.DGFrameCoefficientUnits
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.NativeLargeModuleLifts
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open CochainComplex.HomComplex
open scoped Simplicial

universe u
attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [CommRing k]

/-- All native projective module objects, with their ORIGINAL full homogeneous Hom complexes. -/
def nativeModuleCategory (W : DGCat k) : LocallySmallDG k :=
  ⟨DGDerivedModules k W⟩

/-- The only universe change is the actual native cochain coefficient lift. -/
def largeNativeModuleCategory (L : CochainLiftModel k) (W : DGCat k) : DGCat (LargeScalar k) :=
  liftLocallySmall L (nativeModuleCategory W)

/-- The complete native module category for an ordinary coefficient algebra. -/
def ordinaryModuleCategory (UL : CochainLiftModel k) {T₀ : DGCat k}
    (F : DGFrame k (oppositeCategory T₀)) (N : ShuffleAlgebraFunctor k) (A : CommAlgCat.{u} k) :
    DGCat (LargeScalar k) := largeNativeModuleCategory UL (ordinaryEnvelope F N A)

/-- Native inclusion keeps the original source cochain and every homogeneous map. -/
def qcohIntoGeometric (O : ∀ Z : Scheme.{u}, EtaleStructureSource Z) [SourceTheory.{u}]
    (L : EtalePullbackSystem O) (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A)
    (C : ChartRestrictionSystem O) {X : SourceSpace.{u}} {A : CommRingCat.{u}}
    {π : X.sheaf ⟶ represented.obj (Spec A)} (S : ScalarLinearitySource A π) :
    qcohDGCategory O L J C S ⟶ geometricDG S where
  obj E := E.obj
  map _ _ := 𝟙 _
  map_id _ := by rfl
  map_comp _ _ _ := by
    simp only [Category.comp_id, MonoidalCategory.id_tensorHom_id, Category.id_comp]
    rfl

variable (O : ∀ Z : Scheme.{u}, EtaleStructureSource Z) [SourceTheory.{u}]
    (L : EtalePullbackSystem O) (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A)
    (C : ChartRestrictionSystem O) (D : ProperSpaceSituation.{u}) (B : AffineProperFamily D)
    (SB : ScalarLinearitySource B.ring (affineProperProjection D B)) (UL : CochainLiftModel B.ring)
    (T : SmallPerfectTestModel O L J C SB UL)
    (F : DGFrame B.ring (oppositeCategory T.category))
    {N : ShuffleAlgebraFunctor B.ring} {S : AffineScalarSystem N} (P : StrictPerfectSystem N S)
    (Q : PullbackSystem.{u}) (FB : NativeFramePerfectTests O L J C D B SB UL T F)
    (A : CommAlgCat.{u} B.ring)

/-- One ordinary coefficient source shares the original complete source test realization. -/
structure OrdinaryCoefficientGeometry where
  scalar : ScalarLinearitySource B.ring (baseCoefficientProjection D B A)
  rawPullback : RawPullbackDGSource Q (coefficientSourceMap D B A) B.ring
    (affineProperProjection D B) (baseCoefficientProjection D B A) SB scalar
  tests : TestPullbackDGSource rawPullback (frameTestCategory UL F) FB.functor
  yoneda : GeometricEnvelopingYoneda O L J C D B SB UL T F (N := N) A Q FB scalar rawPullback tests

/-- A full DG quasi-functor roof, normalized to native geometric Yoneda on all modules and all Hom degrees. -/
structure ModuleGeometricRoof (G : OrdinaryCoefficientGeometry O L J C D B SB UL T F Q FB A) where
  source : CofibrantReplacement (ordinaryModuleCategory UL F N A)
  geometric : EnrichedFunctor (Cochains (LargeScalar B.ring)) source.category
    (qcohDGCategory O L J C G.scalar)
  modules : EnrichedFunctor (Cochains (LargeScalar B.ring)) source.category
    (DGDerivedModules (LargeScalar B.ring) (largeOrdinaryEnvelope UL F N A))
  value : ∀ (e : source.category) (x : (ordinaryEnvelope F N A)ᵒᵖ),
    (modules.obj e).obj.toEnrichedFunctor.obj (op (ULift.up x.unop : largeOrdinaryEnvelope UL F N A)) =
      (largeCochainLift B.ring).obj
        (((source.augmentation.obj e).down.obj).toEnrichedFunctor.obj x)
  action : ∀ (e : source.category) (x y : (ordinaryEnvelope F N A)ᵒᵖ)
    (n : ℤ) (a : DGHom B.ring n x y),
    HEq ((modules.obj e).obj.toEnrichedFunctor.dgMap n
      (X := op (ULift.up x.unop : largeOrdinaryEnvelope UL F N A))
      (Y := op (ULift.up y.unop : largeOrdinaryEnvelope UL F N A)) (ULift.up a))
      (homogeneousLift B.ring
        (((source.augmentation.obj e).down.obj).toEnrichedFunctor.dgMap n a))
  homogeneous : ∀ (e e' : source.category) (n : ℤ)
    (a : DGHom (LargeScalar B.ring) n e e') (x : (ordinaryEnvelope F N A)ᵒᵖ),
    HEq (DGFunctor.dgApp (LargeScalar B.ring) (C := (largeOrdinaryEnvelope UL F N A)ᵒᵖ) n
      (op (ULift.up x.unop : largeOrdinaryEnvelope UL F N A)) (modules.dgMap n a))
      (homogeneousLift B.ring (DGFunctor.dgApp B.ring n x ((source.augmentation.dgMap n a).down)))
  comparison : DGNatTrans
    (modules.comp (Cochains (LargeScalar B.ring))
      (cofibrantModulesToRaw (A := B.ring) (largeOrdinaryEnvelope UL F N A)))
    (geometric.comp (Cochains (LargeScalar B.ring)) G.yoneda.functor)
  comparisonWeak : ∀ (e : source.category) (x : (largeOrdinaryEnvelope UL F N A)ᵒᵖ),
    QuasiIso (moduleComponent
      ((DGFunctor.homEquivDGCycles (LargeScalar B.ring) _ _).symm
        ⟨comparison.dgApp e, comparison.dgApp_mem_dgCycles e⟩) x)

/-- The derived realization descends that ENTIRE native DG roof to actual X_A source complexes. -/
structure OrdinaryModuleRealization (G : OrdinaryCoefficientGeometry O L J C D B SB UL T F Q FB A) where
  roof : ModuleGeometricRoof O L J C D B SB UL T F Q FB A G
  moduleProjection : ForgetEnrichment (Cochains (LargeScalar B.ring)) roof.source.category ⥤
    ModuleDerived (fun x : (ordinaryEnvelope F N A)ᵒᵖ => canonicalEvaluation (k := B.ring) x)
  moduleObject : ∀ e : roof.source.category,
    moduleProjection.obj (ForgetEnrichment.of _ e) =
      (moduleQ (fun x : (ordinaryEnvelope F N A)ᵒᵖ => canonicalEvaluation (k := B.ring) x)).obj
        (roof.source.augmentation.obj e).down.obj
  moduleMap : ∀ (e e' : roof.source.category) (a : DGHom (LargeScalar B.ring) 0 e e')
    (ha : a ∈ dgCycles (LargeScalar B.ring) e e'),
    ∃ h : (roof.source.augmentation.dgMap 0 a).down ∈ dgCycles B.ring
      (roof.source.augmentation.obj e).down.obj (roof.source.augmentation.obj e').down.obj,
      moduleProjection.map (dgClosedHomOf (LargeScalar B.ring) a ha) =
        eqToHom (moduleObject e) ≫
        (moduleQ (fun x : (ordinaryEnvelope F N A)ᵒᵖ => canonicalEvaluation (k := B.ring) x)).map
          ((DGFunctor.homEquivDGCycles B.ring _ _).symm
            ⟨(roof.source.augmentation.dgMap 0 a).down, h⟩) ≫ eqToHom (moduleObject e').symm
  geometricProjection : ForgetEnrichment (Cochains (LargeScalar B.ring)) roof.source.category ⥤
    Derived (coefficientSpace D B A)
  geometricObject : ∀ e : roof.source.category,
    geometricProjection.obj (ForgetEnrichment.of _ e) = DerivedCategory.Q.obj (roof.geometric.obj e).obj
  geometricClosed : ∀ (e e' : roof.source.category) (a : DGHom (LargeScalar B.ring) 0 e e')
    (_ha : a ∈ dgCycles (LargeScalar B.ring) e e'),
    roof.geometric.dgMap 0 a ∈ dgCycles (LargeScalar B.ring)
      (roof.geometric.obj e).obj (roof.geometric.obj e').obj
  geometricMap : ∀ (e e' : roof.source.category) (a : DGHom (LargeScalar B.ring) 0 e e')
    (ha : a ∈ dgCycles (LargeScalar B.ring) e e'),
    geometricProjection.map (dgClosedHomOf (LargeScalar B.ring) a ha) =
      eqToHom (geometricObject e) ≫ DerivedCategory.Q.map
        (closedCochainMap G.scalar (roof.geometric.dgMap 0 a) (geometricClosed e e' a ha)) ≫
        eqToHom (geometricObject e').symm
  functor : ModuleDerived (fun x : (ordinaryEnvelope F N A)ᵒᵖ => canonicalEvaluation (k := B.ring) x) ⥤
    Derived (coefficientSpace D B A)
  normalized : moduleProjection ⋙ functor ≅ geometricProjection

/-- Every original module morphism is realized by the same full module localization and source functor. -/
def realizeModuleMap {G : OrdinaryCoefficientGeometry O L J C D B SB UL T F (N := N) Q FB A}
    (R : OrdinaryModuleRealization O L J C D B SB UL T F Q FB A G)
    {V W : RightModule B.ring (ordinaryEnvelope F N A)} (f : V ⟶ W) :=
  R.functor.map ((moduleQ (fun x : (ordinaryEnvelope F N A)ᵒᵖ => canonicalEvaluation (k := B.ring) x)).map f)

/-- The full module RHom leg is the native source DG augmentation in every integer degree. -/
def moduleRealizationRHomLeg {G : OrdinaryCoefficientGeometry O L J C D B SB UL T F (N := N) Q FB A}
    (R : OrdinaryModuleRealization O L J C D B SB UL T F Q FB A G) (x y : R.roof.source.category) :=
  R.roof.source.augmentation.map x y

/-- The geometric RHom leg is the actual enriched realization of the same full source roof. -/
def geometricRealizationRHomLeg {G : OrdinaryCoefficientGeometry O L J C D B SB UL T F (N := N) Q FB A}
    (R : OrdinaryModuleRealization O L J C D B SB UL T F Q FB A G) (x y : R.roof.source.category) :=
  R.roof.geometric.map x y

/-- Smoothness tests the actual original structural chart maps on every native family. -/
def IsSmoothProperSource (D : ProperSpaceSituation.{u}) : Prop :=
  ∀ (T : FamilyTest D) (U : EtaleChart (familySpace D T)),
    Smooth (chartStructuralMap (familyProjection D T) U)

end MathlibExt.AlgebraicGeometry.ProperOrdinaryModuleRealization
