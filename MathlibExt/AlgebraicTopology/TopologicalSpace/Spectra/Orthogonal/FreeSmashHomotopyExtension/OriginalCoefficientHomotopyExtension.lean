/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.OriginalSourceFields
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.OriginalTargetFields
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.EvaluatedFreeScalarKanComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.ScalarKanBoundary

/-!
# Coefficient homotopy extension for orthogonal free smash

Compares the complete free-smash coefficient functor with its shifted left-Kan tensor functor,
including the whole arrows. Realized boundary inclusions give based homotopy extension on both
sides and for every target sphere module.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal FunctionSpectrum
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization
open scoped MonoidalClosed CategoryTheory.MonObj

universe uArrowA vArrowA uArrowC vArrowC

private def comparisonArrow {A : Type uArrowA} [Category.{vArrowA} A]
    {C : Type uArrowC} [Category.{vArrowC} C] {F G : A ⥤ C} (e : F ≅ G)
    {X Y : A} (f : X ⟶ Y) : Arrow.mk (F.map f) ≅ Arrow.mk (G.map f) :=
  ((Functor.mapArrowFunctor A C).mapIso e).app (Arrow.mk f)

attribute [local instance] CanonicalSourceSmash.monoidalCategory
  CanonicalSourceSmash.symmetricCategory CanonicalSourceSmashClosed.monoidalClosed
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.EnrichedKan.hasObjectCoproduct PointedCGWH.EnrichedKan.hasRelationCoproduct
  PointedCGWH.EnrichedKan.hasBalancingCoequalizer
  SphereSmashStructure.indexCategory SphereSmashStructure.indexMonoidalCategory
  SphereSmashStructure.indexEnrichedOrdinaryCategory SphereSmashStructure.indexSymmetricCategory

namespace OrthogonalIGeneratorProbe.NativeHEPJoin

/-- The category of native pointed orthogonal spectra with the canonical source smash
presentation. -/
abbrev Carrier := CanonicalSourceSmash.Carrier.{u, v}

/-- The actual native left mate between families with both exact object and map fields. -/
def comparison (r : OrthogonalIndex) (Y : Carrier.{u, v}) :
    NativeEvaluatedFields.source r Y ≅ NativeEvaluatedTarget.target r Y :=
  eqToIso (NativeEvaluatedFields.source_eq r Y) ≪≫ NativeMateEvaluation.comparison r Y ≪≫
    (eqToIso (NativeEvaluatedTarget.target_eq r Y)).symm

/-- The original comparison component with its complete literal free-smash and scalar Kan objects. -/
def freeSmashScalarKanIso (r : OrthogonalIndex) (K : PointedCGWH.{u, v})
    (Y : Carrier.{u, v}) :
    Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⊗ Y ≅
      (leftKan (RightShift.indexShift.{u, v} r)).obj (tensorLeftObject K Y) :=
  (comparison r Y).app K

/-- The complete coefficient square has a named Arrow isomorphism. -/
def arrow (r : OrthogonalIndex) (Y : Carrier.{u, v})
    {K L : PointedCGWH.{u, v}} (i : K ⟶ L) :
    Arrow.mk ((NativeEvaluatedFields.source r Y).map i) ≅
      Arrow.mk ((NativeEvaluatedTarget.target r Y).map i) :=
  comparisonArrow (comparison r Y) i

theorem target_HEP (r : OrthogonalIndex) {K L : PointedCGWH.{u, v}}
    (i : K ⟶ L) (hi : PointedCGWH.realizedBoundaryInclusions i) (Y : Carrier.{u, v}) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property
      ((NativeEvaluatedTarget.target r Y).map i) := by
  rw [NativeEvaluatedTarget.target_map]
  exact FinalHEPCompatible.scalarKan_boundary r i hi Y

/-- Every original coefficient boundary has HEP in the complete fixed native source family. -/
theorem source_HEP (r : OrthogonalIndex) {K L : PointedCGWH.{u, v}}
    (i : K ⟶ L) (hi : PointedCGWH.realizedBoundaryInclusions i) (Y : Carrier.{u, v}) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property
      ((NativeEvaluatedFields.source r Y).map i) :=
  (PointedCGWH.EnrichedBasedHomotopyExtension.property.arrow_mk_iso_iff
    (arrow r Y i)).mpr (target_HEP r i hi Y)

/-- The exact original free coefficient arrow has HEP after the full native smash with every Y. -/
theorem freeBoundary_smash_HEP (r : OrthogonalIndex) {K L : PointedCGWH.{u, v}}
    (i : K ⟶ L) (hi : PointedCGWH.realizedBoundaryInclusions i) (Y : Carrier.{u, v}) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property
      (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} r) i ▷ Y) := by
  have h := source_HEP r i hi Y
  rw [NativeEvaluatedFields.source_map] at h
  exact h








end OrthogonalIGeneratorProbe.NativeHEPJoin
