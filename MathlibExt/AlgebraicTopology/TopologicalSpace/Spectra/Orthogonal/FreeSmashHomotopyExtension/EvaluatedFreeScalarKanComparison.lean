/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.MorphismProperty.Basic
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FreeScalarKanComparison

/-!
# Evaluated free-smash and scalar Kan comparisons

Evaluating the free-smash/scalar Kan natural isomorphism at any target gives the
corresponding coefficient functor comparison. Every coefficient arrow then has an Arrow
isomorphism with both endpoint comparison maps.
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

namespace OrthogonalIGeneratorProbe.NativeMateEvaluation

/-- The category of native pointed orthogonal spectra with the canonical source smash
presentation. -/
abbrev Carrier := CanonicalSourceSmash.Carrier.{u, v}

/-- Every original coefficient and target is retained when evaluating the actual full left mate. -/
def comparison (r : OrthogonalIndex) (Y : Carrier.{u, v}) :
    (FreeSourceBif.nativeFree.{u, v} r ⋙ curriedTensor Carrier.{u, v}) ⋙
        (evaluation Carrier.{u, v} Carrier.{u, v}).obj Y ≅
      FinalLeftMate.scalarKanFamily.{u, v} r ⋙ (evaluation Carrier.{u, v} Carrier.{u, v}).obj Y :=
  Functor.isoWhiskerRight (FinalLeftMate.freeSmashKanComparison r)
    ((evaluation Carrier.{u, v} Carrier.{u, v}).obj Y)

/-- The original evaluated source and scalar/Kan arrows have a named Arrow isomorphism. -/
def arrow (r : OrthogonalIndex) (Y : Carrier.{u, v})
    {K L : PointedCGWH.{u, v}} (i : K ⟶ L) :
    Arrow.mk (((FreeSourceBif.nativeFree r ⋙ curriedTensor Carrier.{u, v}) ⋙
      (evaluation Carrier.{u, v} Carrier.{u, v}).obj Y).map i) ≅
    Arrow.mk ((FinalLeftMate.scalarKanFamily r ⋙
      (evaluation Carrier.{u, v} Carrier.{u, v}).obj Y).map i) :=
  comparisonArrow (comparison r Y) i




end OrthogonalIGeneratorProbe.NativeMateEvaluation
