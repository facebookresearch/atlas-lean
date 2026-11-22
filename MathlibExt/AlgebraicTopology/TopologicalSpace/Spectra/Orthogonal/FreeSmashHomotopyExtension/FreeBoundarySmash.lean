/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.OriginalCoefficientHomotopyExtension
import Mathlib.Logic.Function.Basic

/-!
# Homotopy extension for free orthogonal boundaries

Smashing the free image of a realized boundary inclusion with an arbitrary orthogonal sphere
module has based enriched homotopy extension. The statement ranges over every orthogonal
operator index through its finite-index representative.
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

universe uIndex uOperator

private theorem fromAllImages {I : Type uIndex} {O : Type uOperator}
    (f : I → O) (g : O → I) (h : ∀ a, f (g a) = a) (P : O → Prop)
    (hp : ∀ r, P (f r)) : ∀ a, P a :=
  (Function.Surjective.forall (f := f) (p := P) (fun a => ⟨g a, h a⟩)).mpr hp

attribute [local instance] CanonicalSourceSmash.monoidalCategory
  CanonicalSourceSmash.symmetricCategory CanonicalSourceSmashClosed.monoidalClosed
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.EnrichedKan.hasObjectCoproduct PointedCGWH.EnrichedKan.hasRelationCoproduct
  PointedCGWH.EnrichedKan.hasBalancingCoequalizer
  SphereSmashStructure.indexCategory SphereSmashStructure.indexMonoidalCategory
  SphereSmashStructure.indexEnrichedOrdinaryCategory SphereSmashStructure.indexSymmetricCategory

namespace OrthogonalIGeneratorProbe.NativeOriginalHEP

/-- The category of native pointed orthogonal spectra with the canonical source smash
presentation. -/
abbrev Carrier := CanonicalSourceSmash.Carrier.{u, v}

theorem ofIndex_asIndex (a : OrthogonalOperatorIndex.{u, v}) :
    OrthogonalOperatorIndex.ofIndex.{u, v} a.asIndex = a := by
  cases a
  rfl

/-- The full original I-generator HEP statement at every native operator and every right spectrum. -/
theorem original_freeBoundary_smash_HEP (a : OrthogonalOperatorIndex.{u, v})
    {K L : PointedCGWH.{u, v}} (i : K ⟶ L)
    (hi : PointedCGWH.realizedBoundaryInclusions i) (Y : Carrier.{u, v}) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property ((Free.coefficientMap a i) ▷ Y) := by
  exact fromAllImages OrthogonalOperatorIndex.ofIndex (fun b => b.asIndex) ofIndex_asIndex
    (fun b => PointedCGWH.EnrichedBasedHomotopyExtension.property (Free.coefficientMap b i ▷ Y))
    (fun r => NativeHEPJoin.freeBoundary_smash_HEP r i hi Y) a




end OrthogonalIGeneratorProbe.NativeOriginalHEP
