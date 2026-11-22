/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FixedTargetMappingFamily
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FixedCoefficientSquare
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeSourceInverse
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.OriginalNativeMappingEquality
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FixedFreeMappingFamily
import MathlibExt.CategoryTheory.Equivalence.FunctorFamily
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FreeMappingFields
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeFreeFunctor
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NormalizedFreeMapping
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NormalizedFreeCoefficients
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeTargetNaturality
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration

/-!
# Free-source internal Hom for orthogonal spectra

The free-source module internal Hom family is transported through the source equivalence
and compared with right-shifted scalar cotensoring. The comparisons retain all
orthogonal indices, coefficients and target diagrams, as well as the complete source and
target functors.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
universe u v
open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open PointedCGWH.Spectra.Orthogonal FunctionSpectrum
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization
open scoped MonoidalClosed CategoryTheory.MonObj

namespace OrthogonalIGeneratorProbe.NativeFixedFamily

/-- The ordinary category of orthogonal indices at the chosen universes. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The tensor of orthogonal indices given by direct sum of their representations. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The pointed enrichment of the orthogonal index category used by its Day tensor. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The symmetry of the orthogonal index tensor given by swapping the representation blocks. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
/-- Day convolution on pointed enriched functors from the orthogonal index. -/
local instance : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  OrthogonalDay.monoidalCategory.{u, v}
/-- The symmetry of orthogonal Day convolution induced by the index block swap. -/
local instance : SymmetricCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  OrthogonalDay.symmetricCategory.{u, v}
/-- The sphere-diagram monoid under orthogonal Day convolution. -/
local instance : MonObj sphereISpace.{u, v} := OrthogonalDay.sphereMonObj.{u, v}
local instance : IsCommMonObj sphereISpace.{u, v} := OrthogonalDay.sphereIsCommMonObj.{u, v}
local instance : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  PointedCGWH.EnrichedMapping.hasSmallLimits.{u, v}
/-- The closed structure on orthogonal Day convolution from the original enriched monoidal index
data. -/
local instance : MonoidalClosed (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  EnrichedDayKernel.Closed.monoidalClosed OrthogonalIndex.enrichedMonoidalData.{u, v}
attribute [local instance] Enriched.prodCategory EnrichedDayKernel.ColimitMonoidal.smallestColimits
  SphereModuleMappingEnd.moduleCategory MonoidalLeftAction.monoidalOppositeLeftAction

open CanonicalSourceRightModuleActions CanonicalSourceRightModuleEquivalence
open EnrichedDayKernel ModuleMappingR
private abbrev d := OrthogonalIndex.enrichedMonoidalData.{u, v}
private abbrev b := OrthogonalIndex.enrichedSymmetricData.{u, v}
private abbrev S := orthogonalSphereFunctor.{u, v}
private abbrev L := orthogonalSphereMonoidalData.{u, v}
private abbrev B := orthogonalSphereBraidedData.{u, v}

/-- The free-source module-Hom output compared with the inverse image of the shifted native
cotensor at one coefficient and target. -/
def element (r : OrthogonalIndex) (K : PointedCGWH.{u, v}ᵒᵖ) (Z : NativeDiagram.{u, v}) :
    ((FixedFreeMapping.family d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r).obj K).obj
        (NativeWholeSource.sourceEquivalence.{u, v}.inverse.obj Z) ≅
      NativeWholeSource.sourceEquivalence.{u, v}.inverse.obj
        ((NativeTargetBoundary.objectFunction.{u, v} r K).obj Z) :=
  NativeWholeSource.element r K Z

set_option maxHeartbeats 500000 in
/-- The free-source mapping family conjugated by the original source equivalence and compared with
the fixed shifted-cotensor family. -/
def comparison (r : OrthogonalIndex) :
    FixedFreeMapping.family d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r ⋙
        (NativeWholeSource.sourceEquivalence.{u, v}.congrLeft.trans
          NativeWholeSource.sourceEquivalence.{u, v}.congrRight).functor ≅
      FixedTarget.family.{u, v} r :=
  Equivalence.conjugateFamilyIso NativeWholeSource.sourceEquivalence.{u, v}
    (FixedFreeMapping.family d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r)
    (FixedTarget.family.{u, v} r) (element r)
    (by
      intro K Z Z' f
      exact NativeWholeSource.target_square r K f)
    (fun {K K'} i Z =>
      FixedCoefficient.square d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
        r i.unop (NativeWholeSource.sourceEquivalence.{u, v}.inverse.obj Z)
        (NativeWholeSource.sourceEquivalence.{u, v}.inverse.obj
          ((NativeTargetBoundary.objectFunction.{u, v} r K').obj Z))
        (NativeWholeSource.sourceEquivalence.{u, v}.inverse.obj
          ((NativeTargetBoundary.objectFunction.{u, v} r K).obj Z))
        (NativeWholeSource.element r K' Z) (NativeWholeSource.element r K Z)
        (NativeWholeSource.sourceEquivalence.{u, v}.inverse.map
          (((FixedTarget.family.{u, v} r).map i).app Z))
        (NativeWholeSource.parameter_square r i Z))

set_option maxHeartbeats 500000 in
/-- The transported source mapping family compared with the original shifted-cotensor family,
retaining the whole source equalities. -/
def sourceComparison (r : OrthogonalIndex) :
    FreeSourceBif.sourceMapping.{u, v} r ≅ NativeTargetBoundary.rawFamily.{u, v} r :=
  eqToIso (OriginalMapping.sourceMapping_eq r) ≪≫
    (Functor.isoWhiskerRight (eqToIso
      (FixedFreeMapping.whole_eq d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r))
      ((equivalence.{u, v}.symm.congrLeft.trans equivalence.{u, v}.symm.congrRight).functor)).symm ≪≫
    (eqToIso (congrArg
      (fun E : Module d.{u, v} S.{u, v} L.{u, v} ≌ NativeDiagram.{u, v} =>
        FixedFreeMapping.family d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r ⋙
          (E.congrLeft.trans E.congrRight).functor) NativeWholeSource.whole_eq.{u, v})).symm ≪≫
    comparison r ≪≫ eqToIso (FixedTarget.whole_eq r)

/-- The native free-source internal Hom family compared with the original right-shifted cotensor
family. -/
def nativeComparison (r : OrthogonalIndex) :
    FreeSourceBif.nativeMapping.{u, v} r ≅ NativeTargetBoundary.rawFamily.{u, v} r :=
  FreeSourceBif.comparison r ≪≫ sourceComparison r






end OrthogonalIGeneratorProbe.NativeFixedFamily
