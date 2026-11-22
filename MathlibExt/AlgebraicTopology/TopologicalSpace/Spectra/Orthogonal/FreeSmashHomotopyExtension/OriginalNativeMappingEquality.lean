/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeFreeFunctor
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FreeMappingFields
import MathlibExt.CategoryTheory.Equivalence.FunctorFamily
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration

/-!
# Native and generic orthogonal source-mapping functors

The native orthogonal free-source mapping functor equals the generic module-mapping family
transported through the module-diagram equivalence. This is an equality of whole functors,
retaining the source and target variances and every coefficient map.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open PointedCGWH.Spectra.Orthogonal FunctionSpectrum
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization
open scoped MonoidalClosed CategoryTheory.MonObj

namespace OrthogonalIGeneratorProbe.OriginalMapping

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

set_option maxHeartbeats 500000 in
-- Transport the whole original free-functor equality through the original module bifunctor and E.
theorem sourceMapping_eq (r : OrthogonalIndex) :
    FreeSourceBif.sourceMapping.{u, v} r =
      FreeMappingGetters.functor d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r ⋙
        (equivalence.{u, v}.symm.congrLeft.trans equivalence.{u, v}.symm.congrRight).functor :=
  congrArg (fun F : PointedCGWH.{u, v} ⥤ SourceModule.{u, v} =>
    F.op ⋙ ModuleMappingR.moduleBifunctor d.{u, v} b.{u, v}
      S.{u, v} L.{u, v} B.{u, v} ⋙ (equivalence.{u, v}.symm.congrLeft.trans equivalence.{u, v}.symm.congrRight).functor)
    (NativeWholeFree.whole_eq r)



end OrthogonalIGeneratorProbe.OriginalMapping
