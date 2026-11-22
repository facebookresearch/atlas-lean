/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FreeScalarKanComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeFreeMappingComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.ParametrizedLeftMate
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.ScalarKanBoundary

/-!
# Coefficient maps of orthogonal free and Kan families

The native free functor sends a coefficient map to `Free.coefficientMap`
at the corresponding orthogonal operator index. The scalar Kan family
sends that map, at every native spectrum, to the right-shift left Kan
extension of its scalar tensor map.
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

attribute [local instance] CanonicalSourceSmash.monoidalCategory
  CanonicalSourceSmash.symmetricCategory CanonicalSourceSmashClosed.monoidalClosed
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.EnrichedKan.hasObjectCoproduct PointedCGWH.EnrichedKan.hasRelationCoproduct
  PointedCGWH.EnrichedKan.hasBalancingCoequalizer
  SphereSmashStructure.indexCategory SphereSmashStructure.indexMonoidalCategory
  SphereSmashStructure.indexEnrichedOrdinaryCategory SphereSmashStructure.indexSymmetricCategory

namespace OrthogonalIGeneratorProbe.FinalGetters

/-- The category of native pointed orthogonal spectra with the canonical source smash
presentation. -/
abbrev Carrier := CanonicalSourceSmash.Carrier.{u, v}

theorem free_map (r : OrthogonalIndex) {K L : PointedCGWH.{u, v}} (i : K ⟶ L) :
    (FreeSourceBif.nativeFree.{u, v} r).map i =
      Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} r) i := rfl

theorem kan_map (r : OrthogonalIndex) {K L : PointedCGWH.{u, v}}
    (i : K ⟶ L) (Y : Carrier.{u, v}) :
    ((FinalLeftMate.scalarKanFamily.{u, v} r).map i).app Y =
      (leftKan (RightShift.indexShift.{u, v} r)).map (scalarTensorMap i Y) := rfl




end OrthogonalIGeneratorProbe.FinalGetters
