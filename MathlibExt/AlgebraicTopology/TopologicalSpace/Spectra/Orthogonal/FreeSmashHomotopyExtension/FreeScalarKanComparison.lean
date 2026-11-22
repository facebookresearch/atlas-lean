/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeFreeMappingComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.ParametrizedLeftMate
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.ScalarKanBoundary

/-!
# Free orthogonal smash and scalar Kan extension

Compares the internal Hom from a free orthogonal spectrum with the right-shifted cotensor family. Its left mate identifies smash with that free spectrum with scalar tensor followed by enriched left Kan extension along the right-shift index functor.
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

namespace OrthogonalIGeneratorProbe.FinalLeftMate

/-- The category of native pointed orthogonal spectra with the canonical source smash
presentation. -/
abbrev Carrier := CanonicalSourceSmash.Carrier.{u, v}

/-- Enriched left Kan extension is left adjoint to restriction along the right-shift index
functor. -/
def shiftAdjunction (r : OrthogonalIndex) :
    leftKan (RightShift.indexShift.{u, v} r) ⊣ RightShift.shift.{u, v} r :=
  leftKanRestrictionAdjunction (RightShift.indexShift r)

/-- The coefficient-indexed family that first tensors a spectrum with the coefficient and then
applies left Kan extension. -/
def scalarKanFamily (r : OrthogonalIndex) : PointedCGWH.{u, v} ⥤ (Carrier.{u, v} ⥤ Carrier.{u, v}) :=
  ParametrizedAdjunction.OriginalPostcomposition.left
    (F := ScalarLeibniz.tensorBifunctor (V := PointedCGWH.{u, v})
      (A := OrthogonalOperatorIndex.{u, v})) (L := leftKan (RightShift.indexShift r))

/-- The free-source internal Hom family is naturally isomorphic to the right-shifted cotensor
family. -/
def rightComparison (r : OrthogonalIndex) :
    (FreeSourceBif.nativeFree.{u, v} r).op ⋙ MonoidalClosed.internalHom ≅
      ParametrizedAdjunction.OriginalPostcomposition.right
        (G := ScalarLeibniz.cotensorBifunctor (V := PointedCGWH.{u, v})
          (A := OrthogonalOperatorIndex.{u, v})) (R := RightShift.shift r) :=
  NativeFixedFamily.nativeComparison r

set_option maxHeartbeats 500000 in
-- The free-smash comparison is the left mate of the shifted-cotensor comparison.
/-- The left mate identifying smash with a free spectrum and left Kan extension of the scalar
tensor. -/
def freeSmashKanComparison (r : OrthogonalIndex) :
    FreeSourceBif.nativeFree.{u, v} r ⋙ curriedTensor Carrier.{u, v} ≅ scalarKanFamily.{u, v} r :=
  ParametrizedMate.comparison (FreeSourceBif.nativeFree r)
    ScalarLeibniz.parametrizedAdjunction (shiftAdjunction r) (rightComparison r)






end OrthogonalIGeneratorProbe.FinalLeftMate
