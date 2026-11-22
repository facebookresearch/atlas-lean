/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Enriched.LeftKanComposition
import MathlibExt.CategoryTheory.Enriched.LeftKanFreeMapData
import MathlibExt.CategoryTheory.Enriched.LeftKanFreeComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SpectrumIndexMaps
import MathlibExt.Topology.Category.PointedCGWH.SmallKanCoends

/-!
# The complete native sequential, symmetric and orthogonal Kan composite

The original sequential-to-symmetric operator functor and full
symmetric-to-orthogonal operator functor are retained on their unchanged
pointed enriched carriers. Prolongation uses the actual weighted coends,
and restriction keeps every original operator action. Both Hom directions,
the complete units/counits and their composition comparisons are preserved.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat MonoidalCategory
open CategoryTheory.Spectra CategoryTheory.Spectra.SpectrumIndexMaps
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.Spectra.NativeIndexKanComposition

attribute [local instance] MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The original sequential sphere-power enrichment on the same native index carrier. -/
local instance sequentialEnrichedCategory :
    EnrichedCategory PointedCGWH.{u, v} PointedCGWH.Spectra.Sequential.Index.{u, v} :=
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory PointedCGWH.sphereOne.{u, v}

private instance nativeRelationCoproducts {A B : Type}
    [EnrichedCategory PointedCGWH.{u, v} A] [EnrichedCategory PointedCGWH.{u, v} B]
    (j : EnrichedFunctor PointedCGWH.{u, v} A B) :
    ∀ (X : EnrichedFunctorCat PointedCGWH.{u, v} A) (b : B),
      HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) X.toEnrichedFunctor) :=
  fun X b => PointedCGWH.EnrichedKan.hasRelationCoproduct (leftKanWeight j b) X.toEnrichedFunctor

private instance nativeObjectCoproducts {A B : Type}
    [EnrichedCategory PointedCGWH.{u, v} A] [EnrichedCategory PointedCGWH.{u, v} B]
    (j : EnrichedFunctor PointedCGWH.{u, v} A B) :
    ∀ (X : EnrichedFunctorCat PointedCGWH.{u, v} A) (b : B),
      HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) X.toEnrichedFunctor) :=
  fun X b => PointedCGWH.EnrichedKan.hasObjectCoproduct (leftKanWeight j b) X.toEnrichedFunctor

private instance nativeBalancingCoequalizers {A B : Type}
    [EnrichedCategory PointedCGWH.{u, v} A] [EnrichedCategory PointedCGWH.{u, v} B]
    (j : EnrichedFunctor PointedCGWH.{u, v} A B) :
    ∀ (X : EnrichedFunctorCat PointedCGWH.{u, v} A) (b : B),
      HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) X.toEnrichedFunctor)
        (Enriched.weightedCoend.rightMap (leftKanWeight j b) X.toEnrichedFunctor) :=
  fun X b => PointedCGWH.EnrichedKan.hasBalancingCoequalizer (leftKanWeight j b) X.toEnrichedFunctor

/-- The original genuine sequential spectrum functor category. -/
abbrev SequentialCarrier :=
  EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.Spectra.Sequential.Index.{u, v}
/-- The original genuine symmetric spectrum functor category. -/
abbrev SymmetricCarrier := EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}
/-- The original genuine orthogonal spectrum functor category. -/
abbrev OrthogonalCarrier := EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}

/-- The complete original N/I free comparison and both source maps are initialized before their public projections. -/
def sequentialOrthogonalFreeData :
    LeftKanFreeComparison.FullMapFamilies.Data sequentialOrthogonalOperatorIndexFunctor.{u, v} :=
  LeftKanFreeComparison.FullMapFamilies.dataOfCoends sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (nativeRelationCoproducts sequentialOrthogonalOperatorIndexFunctor.{u, v})
    (nativeObjectCoproducts sequentialOrthogonalOperatorIndexFunctor.{u, v})
    (nativeBalancingCoequalizers sequentialOrthogonalOperatorIndexFunctor.{u, v})

/-- The whole original N/Sigma prolongation uses the genuine sequential sphere operator map. -/
def sequentialSymmetricLan : SequentialCarrier.{u, v} ⥤ SymmetricCarrier.{u, v} :=
  leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}

/-- The whole original Sigma/I prolongation keeps the original permutation coefficient map. -/
def symmetricOrthogonalLan : SymmetricCarrier.{u, v} ⥤ OrthogonalCarrier.{u, v} :=
  leftKan symmetricOrthogonalOperatorIndexFunctor.{u, v}

/-- The original N/I prolongation uses their complete enriched composite. -/
def sequentialOrthogonalLan : SequentialCarrier.{u, v} ⥤ OrthogonalCarrier.{u, v} :=
  sequentialOrthogonalFreeData.{u, v}.originalLan

/-- Complete N/Sigma restriction on every original enriched transformation and action. -/
def sequentialSymmetricRestriction : SymmetricCarrier.{u, v} ⥤ SequentialCarrier.{u, v} :=
  restriction sequentialSymmetricOperatorIndexFunctor.{u, v}

/-- Complete Sigma/I restriction retains every original permutation action. -/
def symmetricOrthogonalRestriction : OrthogonalCarrier.{u, v} ⥤ SymmetricCarrier.{u, v} :=
  restriction symmetricOrthogonalOperatorIndexFunctor.{u, v}

/-- Complete N/I restriction uses both original enriched operator maps. -/
def sequentialOrthogonalRestriction : OrthogonalCarrier.{u, v} ⥤ SequentialCarrier.{u, v} :=
  restriction sequentialOrthogonalOperatorIndexFunctor.{u, v}

/-- The original first pair is the full weighted-coend adjunction. -/
def sequentialSymmetricAdjunction :
    sequentialSymmetricLan.{u, v} ⊣ sequentialSymmetricRestriction.{u, v} :=
  leftKanRestrictionAdjunction sequentialSymmetricOperatorIndexFunctor.{u, v}

/-- The second pair retains both original full Kan Hom functions. -/
def symmetricOrthogonalAdjunction :
    symmetricOrthogonalLan.{u, v} ⊣ symmetricOrthogonalRestriction.{u, v} :=
  leftKanRestrictionAdjunction symmetricOrthogonalOperatorIndexFunctor.{u, v}

/-- The entire native comparison data type retains the three unchanged original enriched carriers. -/
abbrev NativeComparisonData : Type _ :=
  LeftKanComposition.ComparisonData (V := PointedCGWH.{u, v})
    (A := PointedCGWH.Spectra.Sequential.Index.{u, v})
    (B := PointedCGWH.SymmetricOperatorIndex.{u, v}) (C := OrthogonalOperatorIndex.{u, v})

/-- Initialize the original native coend functors and their comparison in the same whole context. -/
def nativeComparisonData : NativeComparisonData.{u, v} :=
  LeftKanComposition.comparisonData sequentialSymmetricOperatorIndexFunctor.{u, v}
    symmetricOrthogonalOperatorIndexFunctor.{u, v}

/-- The original composite pair on the same full native spectrum carriers. -/
def sequentialOrthogonalAdjunction :
    sequentialOrthogonalLan.{u, v} ⊣ sequentialOrthogonalRestriction.{u, v} :=
  nativeComparisonData.{u, v}.originalAdjunction

/-- Both full restriction functors compose to the original N/I restriction. -/
theorem restriction_composite :
    symmetricOrthogonalRestriction.{u, v} ⋙ sequentialSymmetricRestriction.{u, v} =
      sequentialOrthogonalRestriction.{u, v} :=
  RestrictionInversePair.restriction_comp sequentialSymmetricOperatorIndexFunctor.{u, v}
    symmetricOrthogonalOperatorIndexFunctor.{u, v}

/-- The full native comparison is projected only after all actual functor values are fixed. -/
def prolongationIso :
    nativeComparisonData.{u, v}.functors.prolongationAC ≅
      nativeComparisonData.{u, v}.functors.prolongationAB ⋙
        nativeComparisonData.{u, v}.functors.prolongationBC :=
  nativeComparisonData.{u, v}.comparison

/-- The whole stored native data retains every actual original prolongation functor. -/
theorem nativeComparisonData_prolongations :
    nativeComparisonData.{u, v}.functors.prolongationAB = sequentialSymmetricLan.{u, v} ∧
      nativeComparisonData.{u, v}.functors.prolongationBC = symmetricOrthogonalLan.{u, v} ∧
        nativeComparisonData.{u, v}.functors.prolongationAC = sequentialOrthogonalLan.{u, v} := by
  exact ⟨rfl, rfl, rfl⟩

/-- The original native full restriction functors are the same stored values. -/
theorem nativeComparisonData_restrictions :
    nativeComparisonData.{u, v}.functors.restrictionBA = sequentialSymmetricRestriction.{u, v} ∧
      nativeComparisonData.{u, v}.functors.restrictionCB = symmetricOrthogonalRestriction.{u, v} ∧
        nativeComparisonData.{u, v}.functors.restrictionCA = sequentialOrthogonalRestriction.{u, v} := by
  exact ⟨rfl, rfl, rfl⟩

/-- The actual original single Kan adjunction is projected from the same complete native data. -/
def originalNativeAdjunction :
    nativeComparisonData.{u, v}.functors.prolongationAC ⊣
      nativeComparisonData.{u, v}.functors.restrictionCA :=
  nativeComparisonData.{u, v}.originalAdjunction

/-- The actual two-pair adjunction is projected in that same original source context. -/
def compositeNativeAdjunction :
    nativeComparisonData.{u, v}.functors.prolongationAB ⋙
      nativeComparisonData.{u, v}.functors.prolongationBC ⊣
        nativeComparisonData.{u, v}.functors.restrictionCA :=
  nativeComparisonData.{u, v}.compositeAdjunction

/-- The stored original single adjunction is the entire actual native N/I adjunction, including all maps and
triangles. -/
theorem originalNativeAdjunction_original :
    originalNativeAdjunction.{u, v} = sequentialOrthogonalAdjunction.{u, v} := rfl

/-- The stored composite adjunction is the actual two original coend adjunctions at the same full restriction. -/
theorem compositeNativeAdjunction_original :
    compositeNativeAdjunction.{u, v} =
      LeftKanComposition.composedAdjunction sequentialSymmetricOperatorIndexFunctor.{u, v}
        symmetricOrthogonalOperatorIndexFunctor.{u, v} := rfl

/-- Both complete original Hom functions retain the full native comparison and every source map. -/
theorem nativeHomEquiv (X : SequentialCarrier.{u, v}) (Y : OrthogonalCarrier.{u, v})
    (f : (nativeComparisonData.functors.prolongationAB ⋙
      nativeComparisonData.functors.prolongationBC).obj X ⟶ Y) :
    originalNativeAdjunction.homEquiv X Y (prolongationIso.hom.app X ≫ f) =
      compositeNativeAdjunction.homEquiv X Y f :=
  nativeComparisonData.homEquiv X Y f

/-- The inverse original Hom functions retain the same full native comparison. -/
theorem nativeHomEquivSymm (X : SequentialCarrier.{u, v}) (Y : OrthogonalCarrier.{u, v})
    (f : X ⟶ nativeComparisonData.functors.restrictionCA.obj Y) :
    (originalNativeAdjunction.homEquiv X Y).symm f =
      prolongationIso.hom.app X ≫ (compositeNativeAdjunction.homEquiv X Y).symm f :=
  nativeComparisonData.homEquivSymm X Y f

/-- Every original unit component retains the complete native prolongation and restriction square. -/
theorem nativeUnit (X : SequentialCarrier.{u, v}) :
    originalNativeAdjunction.unit.app X ≫
      nativeComparisonData.functors.restrictionCA.map (prolongationIso.hom.app X) =
        compositeNativeAdjunction.unit.app X :=
  nativeComparisonData.unit X

/-- Every original counit component retains the same full native comparison square. -/
theorem nativeCounit (Y : OrthogonalCarrier.{u, v}) :
    prolongationIso.hom.app (nativeComparisonData.functors.restrictionCA.obj Y) ≫
      compositeNativeAdjunction.counit.app Y = originalNativeAdjunction.counit.app Y :=
  nativeComparisonData.counit Y

/-- The two actual original native adjunctions satisfy both full triangle identities. -/
theorem nativeTriangles (X : SequentialCarrier.{u, v}) (Y : OrthogonalCarrier.{u, v}) :
    (nativeComparisonData.functors.prolongationAB ⋙ nativeComparisonData.functors.prolongationBC).map
      (compositeNativeAdjunction.unit.app X) ≫
        compositeNativeAdjunction.counit.app
          ((nativeComparisonData.functors.prolongationAB ⋙
            nativeComparisonData.functors.prolongationBC).obj X) = 𝟙 _ ∧
    compositeNativeAdjunction.unit.app (nativeComparisonData.functors.restrictionCA.obj Y) ≫
      nativeComparisonData.functors.restrictionCA.map (compositeNativeAdjunction.counit.app Y) = 𝟙 _ :=
  ⟨compositeNativeAdjunction.left_triangle_components X,
    compositeNativeAdjunction.right_triangle_components Y⟩

/-- The complete native component adjunctions are the same original coend adjunction values. -/
theorem nativeComponentAdjunctions_original :
    nativeComparisonData.{u, v}.adjunctionAB = sequentialSymmetricAdjunction.{u, v} ∧
      nativeComparisonData.{u, v}.adjunctionBC = symmetricOrthogonalAdjunction.{u, v} := by
  exact ⟨rfl, rfl⟩

/-- The literal original native composite unit retains the two actual unit maps and restriction transport. -/
theorem nativeCompositeUnit (X : SequentialCarrier.{u, v}) :
    compositeNativeAdjunction.unit.app X =
      nativeComparisonData.adjunctionAB.unit.app X ≫
        nativeComparisonData.functors.restrictionBA.map
          (nativeComparisonData.adjunctionBC.unit.app
            (nativeComparisonData.functors.prolongationAB.obj X)) ≫
          nativeComparisonData.restrictionComparison.hom.app
            ((nativeComparisonData.functors.prolongationAB ⋙
              nativeComparisonData.functors.prolongationBC).obj X) :=
  nativeComparisonData.compositeUnit X

/-- The literal original native composite counit retains both actual counits and the full restriction transport. -/
theorem nativeCompositeCounit (Y : OrthogonalCarrier.{u, v}) :
    compositeNativeAdjunction.counit.app Y =
      (nativeComparisonData.functors.prolongationAB ⋙
        nativeComparisonData.functors.prolongationBC).map
          (nativeComparisonData.restrictionComparison.inv.app Y) ≫
        nativeComparisonData.functors.prolongationBC.map
          (nativeComparisonData.adjunctionAB.counit.app
            (nativeComparisonData.functors.restrictionCB.obj Y)) ≫
              nativeComparisonData.adjunctionBC.counit.app Y :=
  nativeComparisonData.compositeCounit Y

/-- Every original N/Sigma free coefficient functor is prolonged by the actual Kan/free comparison. -/
def sequentialSymmetricFreeIso (n : PointedCGWH.Spectra.Sequential.Index.{u, v}) :
    Free.functor n ⋙ sequentialSymmetricLan.{u, v} ≅
      Free.functor (sequentialSymmetricOperatorIndexFunctor.{u, v}.obj n) :=
  LeftKanFreeComparison.functorIso sequentialSymmetricOperatorIndexFunctor.{u, v} n

/-- Every original Sigma/I free coefficient functor keeps its full original permutation map. -/
def symmetricOrthogonalFreeIso (n : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    Free.functor n ⋙ symmetricOrthogonalLan.{u, v} ≅
      Free.functor (symmetricOrthogonalOperatorIndexFunctor.{u, v}.obj n) :=
  LeftKanFreeComparison.functorIso symmetricOrthogonalOperatorIndexFunctor.{u, v} n

/-- Every original N/I free coefficient functor uses the same full composite operator map. -/
def sequentialOrthogonalFreeIso (n : PointedCGWH.Spectra.Sequential.Index.{u, v}) :
    Free.functor n ⋙ sequentialOrthogonalLan.{u, v} ≅
      Free.functor (sequentialOrthogonalOperatorIndexFunctor.{u, v}.obj n) :=
  sequentialOrthogonalFreeData.{u, v}.comparison n

/-- The original complete free N/Sigma forward map is the actual weighted-coend transpose. -/
theorem sequentialSymmetricFreeIso_hom (n : PointedCGWH.Spectra.Sequential.Index.{u, v})
    (X : PointedCGWH.{u, v}) :
    (sequentialSymmetricFreeIso n).hom.app X =
      LeftKanFreeComparison.hom sequentialSymmetricOperatorIndexFunctor n X :=
  LeftKanFreeComparison.functorIso_hom_app sequentialSymmetricOperatorIndexFunctor.{u, v} n X

/-- The inverse free N/Sigma map is the entire original extension of the Kan identity coefficient. -/
theorem sequentialSymmetricFreeIso_inv (n : PointedCGWH.Spectra.Sequential.Index.{u, v})
    (X : PointedCGWH.{u, v}) :
    (sequentialSymmetricFreeIso n).inv.app X =
      LeftKanFreeComparison.inv sequentialSymmetricOperatorIndexFunctor n X :=
  LeftKanFreeComparison.functorIso_inv_app sequentialSymmetricOperatorIndexFunctor.{u, v} n X

/-- Both original free Sigma/I maps retain the original Kan transpose and inverse extension. -/
theorem symmetricOrthogonalFreeIso_maps (n : PointedCGWH.SymmetricOperatorIndex.{u, v})
    (X : PointedCGWH.{u, v}) :
    (symmetricOrthogonalFreeIso n).hom.app X =
      LeftKanFreeComparison.hom symmetricOrthogonalOperatorIndexFunctor n X ∧
    (symmetricOrthogonalFreeIso n).inv.app X =
      LeftKanFreeComparison.inv symmetricOrthogonalOperatorIndexFunctor n X :=
  ⟨LeftKanFreeComparison.functorIso_hom_app symmetricOrthogonalOperatorIndexFunctor.{u, v} n X,
    LeftKanFreeComparison.functorIso_inv_app symmetricOrthogonalOperatorIndexFunctor.{u, v} n X⟩

/-- Both original free N/I map equations retain every original index and coefficient in the same complete data. -/
theorem sequentialOrthogonalFreeIso_maps (n : PointedCGWH.Spectra.Sequential.Index.{u, v})
    (X : PointedCGWH.{u, v}) :
    (sequentialOrthogonalFreeData.comparison n).hom.app X = sequentialOrthogonalFreeData.homMap n X ∧
    (sequentialOrthogonalFreeData.comparison n).inv.app X = sequentialOrthogonalFreeData.invMap n X :=
  ⟨sequentialOrthogonalFreeData.homEquation n X, sequentialOrthogonalFreeData.invEquation n X⟩

/-- Arbitrary based coefficient maps retain the complete original N/Sigma natural square. -/
theorem sequentialSymmetricFreeIso_naturality (n : PointedCGWH.Spectra.Sequential.Index.{u, v})
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (Free.functor n ⋙ sequentialSymmetricLan).map f ≫ (sequentialSymmetricFreeIso n).hom.app Y =
      (sequentialSymmetricFreeIso n).hom.app X ≫
        (Free.functor (sequentialSymmetricOperatorIndexFunctor.obj n)).map f :=
  (sequentialSymmetricFreeIso n).hom.naturality f

/-- Arbitrary based coefficient maps retain the complete original Sigma/I natural square. -/
theorem symmetricOrthogonalFreeIso_naturality (n : PointedCGWH.SymmetricOperatorIndex.{u, v})
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (Free.functor n ⋙ symmetricOrthogonalLan).map f ≫ (symmetricOrthogonalFreeIso n).hom.app Y =
      (symmetricOrthogonalFreeIso n).hom.app X ≫
        (Free.functor (symmetricOrthogonalOperatorIndexFunctor.obj n)).map f :=
  (symmetricOrthogonalFreeIso n).hom.naturality f

/-- Arbitrary based coefficient maps retain the complete original N/I natural square. -/
theorem sequentialOrthogonalFreeIso_naturality (n : PointedCGWH.Spectra.Sequential.Index.{u, v})
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (Free.functor n ⋙ sequentialOrthogonalLan).map f ≫ (sequentialOrthogonalFreeIso n).hom.app Y =
      (sequentialOrthogonalFreeIso n).hom.app X ≫
        (Free.functor (sequentialOrthogonalOperatorIndexFunctor.obj n)).map f :=
  (sequentialOrthogonalFreeIso n).hom.naturality f

/-- The entire sequentialSymmetric free source comparison is initialized with both full map families. -/
def sequentialSymmetricFreeData : LeftKanFreeComparison.FullMapFamilies.Data
      sequentialSymmetricOperatorIndexFunctor.{u, v} :=
  LeftKanFreeComparison.FullMapFamilies.data sequentialSymmetricOperatorIndexFunctor.{u, v}

/-- Every original enriched index source map and coefficient preserves both complete sequentialSymmetric free
comparison directions. -/
theorem sequentialSymmetricFreeIso_source {a a' : PointedCGWH.Spectra.Sequential.Index.{u, v}}
    (e : 𝟙_ (PointedCGWH.{u, v}) ⟶ (a ⟶[PointedCGWH.{u, v}] a'))
    (X : PointedCGWH.{u, v}) :
    sequentialSymmetricFreeData.originalLan.map (Free.sourceMap e X) ≫ sequentialSymmetricFreeData.homMap a X =
      sequentialSymmetricFreeData.homMap a' X ≫ Free.sourceMap (e ≫
      sequentialSymmetricOperatorIndexFunctor.map a a') X ∧
    Free.sourceMap (e ≫ sequentialSymmetricOperatorIndexFunctor.map a a') X ≫ sequentialSymmetricFreeData.invMap a X =
      sequentialSymmetricFreeData.invMap a' X ≫ sequentialSymmetricFreeData.originalLan.map (Free.sourceMap e X) :=
  ⟨sequentialSymmetricFreeData.homSource e X, sequentialSymmetricFreeData.invSource e X⟩

/-- The entire symmetricOrthogonal free source comparison is initialized with both full map families. -/
def symmetricOrthogonalFreeData : LeftKanFreeComparison.FullMapFamilies.Data
      symmetricOrthogonalOperatorIndexFunctor.{u, v} :=
  LeftKanFreeComparison.FullMapFamilies.data symmetricOrthogonalOperatorIndexFunctor.{u, v}

/-- Every original enriched index source map and coefficient preserves both complete symmetricOrthogonal free
comparison directions. -/
theorem symmetricOrthogonalFreeIso_source {a a' : PointedCGWH.SymmetricOperatorIndex.{u, v}}
    (e : 𝟙_ (PointedCGWH.{u, v}) ⟶ (a ⟶[PointedCGWH.{u, v}] a'))
    (X : PointedCGWH.{u, v}) :
    symmetricOrthogonalFreeData.originalLan.map (Free.sourceMap e X) ≫ symmetricOrthogonalFreeData.homMap a X =
      symmetricOrthogonalFreeData.homMap a' X ≫ Free.sourceMap (e ≫
      symmetricOrthogonalOperatorIndexFunctor.map a a') X ∧
    Free.sourceMap (e ≫ symmetricOrthogonalOperatorIndexFunctor.map a a') X ≫ symmetricOrthogonalFreeData.invMap a X =
      symmetricOrthogonalFreeData.invMap a' X ≫ symmetricOrthogonalFreeData.originalLan.map (Free.sourceMap e X) :=
  ⟨symmetricOrthogonalFreeData.homSource e X, symmetricOrthogonalFreeData.invSource e X⟩

/-- Every original enriched index source map and coefficient preserves both complete sequentialOrthogonal free
comparison directions. -/
theorem sequentialOrthogonalFreeIso_source {a a' : PointedCGWH.Spectra.Sequential.Index.{u, v}}
    (e : 𝟙_ (PointedCGWH.{u, v}) ⟶ (a ⟶[PointedCGWH.{u, v}] a'))
    (X : PointedCGWH.{u, v}) :
    sequentialOrthogonalFreeData.originalLan.map (Free.sourceMap e X) ≫ sequentialOrthogonalFreeData.homMap a X =
      sequentialOrthogonalFreeData.homMap a' X ≫ Free.sourceMap (e ≫
      sequentialOrthogonalOperatorIndexFunctor.map a a') X ∧
    Free.sourceMap (e ≫ sequentialOrthogonalOperatorIndexFunctor.map a a') X ≫ sequentialOrthogonalFreeData.invMap a X =
      sequentialOrthogonalFreeData.invMap a' X ≫ sequentialOrthogonalFreeData.originalLan.map (Free.sourceMap e X) :=
  ⟨sequentialOrthogonalFreeData.homSource e X, sequentialOrthogonalFreeData.invSource e X⟩

end PointedCGWH.Spectra.NativeIndexKanComposition
