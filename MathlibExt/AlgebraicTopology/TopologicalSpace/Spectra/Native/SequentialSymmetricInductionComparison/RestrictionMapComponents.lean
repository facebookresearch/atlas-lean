/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.RestrictionSpectrumAndObject

/-!
# Components of sequential restriction maps

Both the module presentation and enriched-index presentation of
sequential restriction send a symmetric spectrum map to its component
at the finite cardinal of the given degree. These formulas identify the
restricted maps through the sequential and symmetric module equivalences.
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

/-- Every original direct module restriction map keeps its complete symmetric operator component. -/
theorem directModuleRestriction_inverse_map_component
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}}
    (f : F ⟶ G) (n : ℕ) :
    EnrichedFunctorCat.component
      (sequentialModuleEquivalence.{u, v}.inverse.map
        ((directModuleRestriction.{u, v}).map
          ((PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse.map f)))
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne.{u, v} n) =
      EnrichedFunctorCat.component f
        (PointedCGWH.symmetricOperatorObj.{u, v} (card n)) := by
  have h := CategoryTheory.SequentialSpectrum.EnrichedPresentation.toEnrichedFunctorMap_component
    PointedCGWH.sphereOne.{u, v}
    ((CategoryTheory.SequentialSpectrum.fromTensorPowerModule PointedCGWH.sphereOne.{u, v}).map
      ((directModuleRestriction.{u, v}).map
        ((PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse.map f)))
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne.{u, v} n)
  exact h.trans (PointedCGWH.symmetricSequenceRestriction_component.{u, v} f
    (degreeInclusion.obj (CategoryTheory.Sequence.index n)))

/-- Every original native restriction map keeps the same complete symmetric operator component. -/
theorem nativeSequentialSymmetricRestriction_map_component
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}}
    (f : F ⟶ G) (n : ℕ) :
    EnrichedFunctorCat.component
      (NativeIndexKanComposition.sequentialSymmetricRestriction.{u, v}.map f)
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne.{u, v} n) =
      EnrichedFunctorCat.component f
        (PointedCGWH.symmetricOperatorObj.{u, v} (card n)) :=
  EnrichedFunctorCat.restrictionMap_component sequentialSymmetricOperatorIndexFunctor.{u, v} f _

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
