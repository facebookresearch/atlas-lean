/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.SelectedRightKan
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Quillen
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.CanonicalStableModelConsumers
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeSymmetricStableLocalization
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeOrthogonalStableLocalization
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.OmegaHomTestTransport
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.IndexKanComposition
import MathlibExt.Topology.Category.CGWH.Limits

/-!
# Original native localization maps and stable adjunction descent

The actual native restrictions preserve local-fibrant Omega objects for all
three adopted index pairs. Their actual coend images of every original
stabilization arrow are local equivalences, using the already constructed
native localization records. The original chosen derived mapping
precomposition maps are weak at every original local-fibrant or Omega target.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential
open PointedCGWH.Spectra.NativeIndexKanComposition
open PointedCGWH.Spectra.NativeStableModelConsumers
open PointedCGWH.Spectra.Orthogonal.IndexKan
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

namespace PointedCGWH.Spectra.NativeStableIndexAdjunctions

private instance basedLimits : HasLimitsOfSize.{v, v} PointedCGWH.{u, v} := by
  change HasLimitsOfSize.{v, v} (Under CGWH.point.{u, v})
  infer_instance

private instance basedProducts : ∀ J : Type v,
    HasLimitsOfShape (Discrete J) PointedCGWH.{u, v} := fun _ => by infer_instance

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] Native.modelCategory SimplicialEnrichment.simplicialCategory
  SingularMapping.cofibrantFactorization SingularMapping.fibrantFactorization

private theorem native_levelKan_isQuillen
    {A D : Type} [EnrichedCategory PointedCGWH.{u, v} A]
    [EnrichedCategory PointedCGWH.{u, v} D]
    (j : EnrichedFunctor PointedCGWH.{u, v} A D) :
    (leftKanRestrictionAdjunction j).IsQuillenAdjunction := by
  have h := Kan.leftKanRestriction_isQuillen j
  dsimp only at h
  rw [Construction.modelCategory_eq_native (B := B) (A := A),
    Construction.modelCategory_eq_native (B := B) (A := D)] at h
  exact h

/-- Complete native N restriction preserves the actual derived-local fibrant objects. -/
theorem sequentialOrthogonal_preservesLocalFibrant
    (E : Actual.OrthogonalCarrier.{u, v})
    (hE : isLocalFibrant StableModelConstruction.orthogonalStabilizationArrows E) :
    isLocalFibrant sequentialStabilizationArrows (sequentialOrthogonalRestriction.obj E) :=
  (DerivedLocalMapping.isLocalFibrant_iff_isOmega
    PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family _).mpr
      ((sequentialRestriction_isOmega_iff E).mpr
        ((StableModelConstruction.orthogonalLocalFibrant_iff_isOmega E).mp hE))

/-- Complete native permutation restriction preserves the actual full-family local objects. -/
theorem symmetricOrthogonal_preservesLocalFibrant
    (E : Actual.OrthogonalCarrier.{u, v})
    (hE : isLocalFibrant StableModelConstruction.orthogonalStabilizationArrows E) :
    isLocalFibrant StableModelConstruction.symmetricStabilizationArrows
      (symmetricOrthogonalRestriction.obj E) :=
  (StableModelConstruction.symmetricLocalFibrant_iff_isOmega _).mpr
    ((symmetricRestriction_isOmega_iff E).mpr
      ((StableModelConstruction.orthogonalLocalFibrant_iff_isOmega E).mp hE))

/-- Original N/Sigma forgetting preserves every original local-fibrant target. -/
theorem sequentialSymmetric_preservesLocalFibrant
    (E : Actual.SymmetricCarrier.{u, v})
    (hE : isLocalFibrant StableModelConstruction.symmetricStabilizationArrows E) :
    isLocalFibrant sequentialStabilizationArrows (sequentialSymmetricRestriction.obj E) :=
  (DerivedLocalMapping.isLocalFibrant_iff_isOmega
    PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family _).mpr
      ((sequential_isOmega_iff _).mpr
        (sequentialSymmetric_isOmega_of_isOmega E
          ((StableModelConstruction.symmetricLocalFibrant_iff_isOmega E).mp hE)))



/-- The original topological N/Sigma coend sends every original stabilization into the local weak class. -/
theorem sequentialSymmetric_localizingMapImage (n : ℕ) :
    localEquivalences (C := Actual.SymmetricCarrier.{u, v})
      StableModelConstruction.symmetricStabilizationArrows
      (sequentialSymmetricLan.map (sequentialStabilizationArrows n).hom) := by
  let : sequentialSymmetricAdjunction.{u, v}.IsQuillenAdjunction :=
    native_levelKan_isQuillen CategoryTheory.Spectra.SpectrumIndexMaps.sequentialSymmetricOperatorIndexFunctor
  exact LeftLocalized.image_localizingMap_of_cofibrant
    sequentialLeftBousfieldLocalizationData
    StableModelConstruction.symmetricLeftBousfieldLocalizationData
    sequentialSymmetricAdjunction sequentialSymmetric_preservesLocalFibrant n
    (NativeK.stabilization_source_cofibrant
      PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family n)
    (NativeK.stabilization_target_cofibrant
      PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family n)

/-- Actual chosen derived mapping precomposition on the full original N/I image is weak at every local target. -/
theorem sequentialOrthogonal_localizingMapImage_derivedWeak
    (n : ℕ) (E : Actual.OrthogonalCarrier.{u, v})
    (hE : isLocalFibrant StableModelConstruction.orthogonalStabilizationArrows E) :
    SSet.realizationWeakEquivalences
      (derivedMappingPrecomp (C := Actual.OrthogonalCarrier.{u, v})
        (sequentialOrthogonalLan.map (sequentialStabilizationArrows n).hom) E) :=
  sequentialLan_stabilization_localEquivalence (B := B) n E hE

/-- Every original Sigma/I source pair has weak actual derived precomposition at every local target. -/
theorem symmetricOrthogonal_localizingMapImage_derivedWeak
    (l : CategoryTheory.Operad.SmallFinBijGroupoid × CategoryTheory.Operad.SmallFinBijGroupoid)
    (E : Actual.OrthogonalCarrier.{u, v})
    (hE : isLocalFibrant StableModelConstruction.orthogonalStabilizationArrows E) :
    SSet.realizationWeakEquivalences
      (derivedMappingPrecomp (C := Actual.OrthogonalCarrier.{u, v})
        (symmetricOrthogonalLan.map (StableModelConstruction.symmetricStabilizationArrows l).hom) E) :=
  symmetricLan_stabilization_localEquivalence (B := B) l.1 l.2 E hE

/-- Every original N/Sigma source degree retains its weak actual derived precomposition. -/
theorem sequentialSymmetric_localizingMapImage_derivedWeak
    (n : ℕ) (E : Actual.SymmetricCarrier.{u, v})
    (hE : isLocalFibrant StableModelConstruction.symmetricStabilizationArrows E) :
    SSet.realizationWeakEquivalences
      (derivedMappingPrecomp (C := Actual.SymmetricCarrier.{u, v})
        (sequentialSymmetricLan.map (sequentialStabilizationArrows n).hom) E) :=
  sequentialSymmetric_localizingMapImage n E hE

/-- The full original N/I image uses the same actual derived mapping map at every native Omega target. -/
theorem sequentialOrthogonal_localizingMapImage_derivedWeak_of_isOmega
    (n : ℕ) (E : Actual.OrthogonalCarrier.{u, v})
    (hE : NativeK.IsOmega Actual.orthogonalFamily E) :
    SSet.realizationWeakEquivalences
      (derivedMappingPrecomp (C := Actual.OrthogonalCarrier.{u, v})
        (sequentialOrthogonalLan.map (sequentialStabilizationArrows n).hom) E) :=
  sequentialOrthogonal_localizingMapImage_derivedWeak n E
    ((StableModelConstruction.orthogonalLocalFibrant_iff_isOmega E).mpr hE)

/-- All source labels and chosen derived maps remain in the native Sigma/I Omega-target assertion. -/
theorem symmetricOrthogonal_localizingMapImage_derivedWeak_of_isOmega
    (l : CategoryTheory.Operad.SmallFinBijGroupoid × CategoryTheory.Operad.SmallFinBijGroupoid)
    (E : Actual.OrthogonalCarrier.{u, v})
    (hE : NativeK.IsOmega Actual.orthogonalFamily E) :
    SSet.realizationWeakEquivalences
      (derivedMappingPrecomp (C := Actual.OrthogonalCarrier.{u, v})
        (symmetricOrthogonalLan.map (StableModelConstruction.symmetricStabilizationArrows l).hom) E) :=
  symmetricOrthogonal_localizingMapImage_derivedWeak l E
    ((StableModelConstruction.orthogonalLocalFibrant_iff_isOmega E).mpr hE)

/-- The full original N/Sigma map is tested at every full-family native Omega target. -/
theorem sequentialSymmetric_localizingMapImage_derivedWeak_of_isOmega
    (n : ℕ) (E : Actual.SymmetricCarrier.{u, v})
    (hE : NativeK.IsOmega Actual.symmetricFamily E) :
    SSet.realizationWeakEquivalences
      (derivedMappingPrecomp (C := Actual.SymmetricCarrier.{u, v})
        (sequentialSymmetricLan.map (sequentialStabilizationArrows n).hom) E) :=
  sequentialSymmetric_localizingMapImage_derivedWeak n E
    ((StableModelConstruction.symmetricLocalFibrant_iff_isOmega E).mpr hE)




/-- The actual topological N/Sigma adjunction descends using its proved original local objects. -/
theorem sequentialSymmetric_localized_isQuillen :
    (LeftLocalized.adjunction sequentialLeftBousfieldLocalizationData
      StableModelConstruction.symmetricLeftBousfieldLocalizationData
      sequentialSymmetricAdjunction.{u, v}).IsQuillenAdjunction := by
  let : sequentialSymmetricAdjunction.{u, v}.IsQuillenAdjunction :=
    native_levelKan_isQuillen CategoryTheory.Spectra.SpectrumIndexMaps.sequentialSymmetricOperatorIndexFunctor
  exact LeftLocalized.isQuillenAdjunction_of_preservesLocalFibrant
    sequentialLeftBousfieldLocalizationData StableModelConstruction.symmetricLeftBousfieldLocalizationData
    sequentialSymmetricAdjunction sequentialSymmetric_preservesLocalFibrant

end PointedCGWH.Spectra.NativeStableIndexAdjunctions
