/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.RestrictionComparison
import MathlibExt.CategoryTheory.Adjunction.RightIsoComparison

/-!
# Sequential-symmetric induction and left Kan extension

The native sequential-to-symmetric induction functor is naturally isomorphic to the
corresponding left Kan extension. Together with the restriction comparison, this identifies
the two adjunction Hom equivalences and their units and counits. The file retains both
comparison inverses, all naturality equations and the triangle identities of both
adjunctions.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open CategoryTheory.Spectra.SpectrumIndexMaps
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison
universe u v
attribute [local instance] PointedCGWH.EnrichedKan.hasSmallColimits
  originalSymmetricSequenceMonoidal originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  degreeInclusionMonoidal restrictionLaxMonoidal symmetrizationOplaxMonoidal sequenceAdjunctionIsMonoidal
  symmetrizationMonoidal orderedSphereMonObj sphereSequenceMonObj
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The original balanced induction and the actual full weighted-coend Kan functor have both comparison directions. -/
def nativeLanComparison : V.{u, v} ≅ NativeIndexKanComposition.sequentialSymmetricLan.{u, v} :=
  CategoryTheory.Adjunction.RightIsoComparison.comparison VWAdjunction.{u, v}
    NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v} nativeRestrictionComparison.{u, v}

/-- Both complete actual forward Hom functions agree through the original whole left and right comparisons. -/
theorem nativeLanComparison_homEquiv
    (X : NativeIndexKanComposition.SequentialCarrier.{u, v})
    (Y : NativeIndexKanComposition.SymmetricCarrier.{u, v})
    (f : NativeIndexKanComposition.sequentialSymmetricLan.{u, v}.obj X ⟶ Y) :
    VWAdjunction.{u, v}.homEquiv X Y (nativeLanComparison.hom.app X ≫ f) ≫
      nativeRestrictionComparison.hom.app Y =
      NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v}.homEquiv X Y f :=
  CategoryTheory.Adjunction.RightIsoComparison.forward VWAdjunction.{u, v}
    NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v}
    nativeRestrictionComparison.{u, v} X Y f

/-- Both complete actual inverse Hom functions agree through the original whole inverse comparisons. -/
theorem nativeLanComparison_homEquiv_symm
    (X : NativeIndexKanComposition.SequentialCarrier.{u, v})
    (Y : NativeIndexKanComposition.SymmetricCarrier.{u, v})
    (g : X ⟶ NativeIndexKanComposition.sequentialSymmetricRestriction.{u, v}.obj Y) :
    (VWAdjunction.{u, v}.homEquiv X Y).symm (g ≫ nativeRestrictionComparison.inv.app Y) =
      nativeLanComparison.hom.app X ≫
        (NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v}.homEquiv X Y).symm g :=
  CategoryTheory.Adjunction.RightIsoComparison.inverse VWAdjunction.{u, v}
    NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v}
    nativeRestrictionComparison.{u, v} X Y g

/-- The full original unit agrees with the complete actual native Kan unit through both comparisons. -/
theorem nativeLanComparison_unit (X : NativeIndexKanComposition.SequentialCarrier.{u, v}) :
    VWAdjunction.{u, v}.unit.app X ≫ nativeRestrictionComparison.hom.app (V.obj X) ≫
      NativeIndexKanComposition.sequentialSymmetricRestriction.map (nativeLanComparison.hom.app X) =
      NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v}.unit.app X :=
  CategoryTheory.Adjunction.RightIsoComparison.unit VWAdjunction.{u, v}
    NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v} nativeRestrictionComparison.{u, v} X

/-- The full original counit agrees with the complete actual native Kan counit through both comparisons. -/
theorem nativeLanComparison_counit (Y : NativeIndexKanComposition.SymmetricCarrier.{u, v}) :
    nativeLanComparison.hom.app (NativeIndexKanComposition.sequentialSymmetricRestriction.obj Y) ≫
      NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v}.counit.app Y =
      V.map (nativeRestrictionComparison.inv.app Y) ≫ VWAdjunction.{u, v}.counit.app Y :=
  CategoryTheory.Adjunction.RightIsoComparison.counit VWAdjunction.{u, v}
    NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v} nativeRestrictionComparison.{u, v} Y

/-- The full inverse left comparison preserves the same original and native unit maps. -/
theorem nativeLanComparison_inv_unit (X : NativeIndexKanComposition.SequentialCarrier.{u, v}) :
    NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v}.unit.app X ≫
      NativeIndexKanComposition.sequentialSymmetricRestriction.map (nativeLanComparison.inv.app X) =
      VWAdjunction.{u, v}.unit.app X ≫ nativeRestrictionComparison.hom.app (V.obj X) :=
  CategoryTheory.Adjunction.RightIsoComparison.inverse_unit VWAdjunction.{u, v}
    NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v} nativeRestrictionComparison.{u, v} X

/-- The full inverse left comparison preserves the same original and native counit maps. -/
theorem nativeLanComparison_inv_counit (Y : NativeIndexKanComposition.SymmetricCarrier.{u, v}) :
    nativeLanComparison.inv.app (NativeIndexKanComposition.sequentialSymmetricRestriction.obj Y) ≫
      V.map (nativeRestrictionComparison.inv.app Y) ≫ VWAdjunction.{u, v}.counit.app Y =
      NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v}.counit.app Y :=
  CategoryTheory.Adjunction.RightIsoComparison.inverse_counit VWAdjunction.{u, v}
    NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v} nativeRestrictionComparison.{u, v} Y

/-- Every original sequential transformation is natural for the entire forward induction comparison. -/
theorem nativeLanComparison_hom_naturality
    {X Y : NativeIndexKanComposition.SequentialCarrier.{u, v}} (f : X ⟶ Y) :
    V.map f ≫ nativeLanComparison.hom.app Y =
      nativeLanComparison.hom.app X ≫ NativeIndexKanComposition.sequentialSymmetricLan.map f :=
  nativeLanComparison.hom.naturality f

/-- Every original sequential transformation is natural for the entire inverse induction comparison. -/
theorem nativeLanComparison_inv_naturality
    {X Y : NativeIndexKanComposition.SequentialCarrier.{u, v}} (f : X ⟶ Y) :
    NativeIndexKanComposition.sequentialSymmetricLan.map f ≫ nativeLanComparison.inv.app Y =
      nativeLanComparison.inv.app X ≫ V.map f := nativeLanComparison.inv.naturality f

/-- Every original symmetric transformation is natural for the entire forward restriction comparison. -/
theorem nativeRestrictionComparison_hom_naturality
    {X Y : NativeIndexKanComposition.SymmetricCarrier.{u, v}} (f : X ⟶ Y) :
    W.map f ≫ nativeRestrictionComparison.hom.app Y =
      nativeRestrictionComparison.hom.app X ≫ NativeIndexKanComposition.sequentialSymmetricRestriction.map f :=
  nativeRestrictionComparison.hom.naturality f

/-- Every original symmetric transformation is natural for the entire inverse restriction comparison. -/
theorem nativeRestrictionComparison_inv_naturality
    {X Y : NativeIndexKanComposition.SymmetricCarrier.{u, v}} (f : X ⟶ Y) :
    NativeIndexKanComposition.sequentialSymmetricRestriction.map f ≫ nativeRestrictionComparison.inv.app Y =
      nativeRestrictionComparison.inv.app X ≫ W.map f := nativeRestrictionComparison.inv.naturality f

/-- Both whole left and right comparison functions recover every full original source and target map. -/
theorem nativeComparison_inverses
    (X : NativeIndexKanComposition.SequentialCarrier.{u, v})
    (Y : NativeIndexKanComposition.SymmetricCarrier.{u, v}) :
    nativeLanComparison.hom.app X ≫ nativeLanComparison.inv.app X = 𝟙 (V.obj X) ∧
    nativeLanComparison.inv.app X ≫ nativeLanComparison.hom.app X =
      𝟙 (NativeIndexKanComposition.sequentialSymmetricLan.obj X) ∧
    nativeRestrictionComparison.hom.app Y ≫ nativeRestrictionComparison.inv.app Y = 𝟙 (W.obj Y) ∧
    nativeRestrictionComparison.inv.app Y ≫ nativeRestrictionComparison.hom.app Y =
      𝟙 (NativeIndexKanComposition.sequentialSymmetricRestriction.obj Y) :=
  ⟨nativeLanComparison.hom_inv_id_app X, nativeLanComparison.inv_hom_id_app X,
    nativeRestrictionComparison.hom_inv_id_app Y, nativeRestrictionComparison.inv_hom_id_app Y⟩

/-- Both full original and native adjunctions satisfy all four original triangle equations. -/
theorem nativeAdjunction_triangles
    (X : NativeIndexKanComposition.SequentialCarrier.{u, v})
    (Y : NativeIndexKanComposition.SymmetricCarrier.{u, v}) :
    V.map (VWAdjunction.{u, v}.unit.app X) ≫ VWAdjunction.counit.app (V.obj X) = 𝟙 (V.obj X) ∧
    VWAdjunction.unit.app (W.obj Y) ≫ W.map (VWAdjunction.counit.app Y) = 𝟙 (W.obj Y) ∧
    NativeIndexKanComposition.sequentialSymmetricLan.map
      (NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v}.unit.app X) ≫
      NativeIndexKanComposition.sequentialSymmetricAdjunction.counit.app
        (NativeIndexKanComposition.sequentialSymmetricLan.obj X) =
      𝟙 (NativeIndexKanComposition.sequentialSymmetricLan.obj X) ∧
    NativeIndexKanComposition.sequentialSymmetricAdjunction.unit.app
      (NativeIndexKanComposition.sequentialSymmetricRestriction.obj Y) ≫
      NativeIndexKanComposition.sequentialSymmetricRestriction.map
        (NativeIndexKanComposition.sequentialSymmetricAdjunction.counit.app Y) =
      𝟙 (NativeIndexKanComposition.sequentialSymmetricRestriction.obj Y) :=
  ⟨VWAdjunction.{u, v}.left_triangle_components X, VWAdjunction.{u, v}.right_triangle_components Y,
    NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v}.left_triangle_components X,
    NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v}.right_triangle_components Y⟩

/-- Every original sequential map preserves the full actual native Kan unit. -/
theorem nativeUnit_naturality
    {X Y : NativeIndexKanComposition.SequentialCarrier.{u, v}} (f : X ⟶ Y) :
    f ≫ NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v}.unit.app Y =
      NativeIndexKanComposition.sequentialSymmetricAdjunction.unit.app X ≫
        NativeIndexKanComposition.sequentialSymmetricRestriction.map
          (NativeIndexKanComposition.sequentialSymmetricLan.map f) :=
  NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v}.unit.naturality f

/-- Every original symmetric map preserves the full actual native Kan counit. -/
theorem nativeCounit_naturality
    {X Y : NativeIndexKanComposition.SymmetricCarrier.{u, v}} (f : X ⟶ Y) :
    NativeIndexKanComposition.sequentialSymmetricLan.map
      (NativeIndexKanComposition.sequentialSymmetricRestriction.map f) ≫
      NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v}.counit.app Y =
      NativeIndexKanComposition.sequentialSymmetricAdjunction.counit.app X ≫ f :=
  NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v}.counit.naturality f

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
