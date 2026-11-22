/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.WholeFreeFunctorTransport
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeFreeMappingBifunctor
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration

/-!
# Free orthogonal modules through the source equivalence

Identifies the complete transported free functor at every orthogonal index with the native
free-module construction. Both functor equality and the corresponding dependent equality retain
its objects and maps.
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

namespace OrthogonalIGeneratorProbe.NativeWholeFree

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

/-- The primitive free right-module functor built from the original orthogonal Day tensor and
sphere monoid. -/
def rawFree (r : OrthogonalIndex) :=
  letI := ColimitMonoidal.monoidalCategory d.{u, v}
  letI : MonObj (⟨S.{u, v}⟩ : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
    LaxMonoid.monObj d.{u, v} S.{u, v} L.{u, v}
  CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free
    (⟨S.{u, v}⟩ : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) r

set_option maxHeartbeats 500000 in
-- Eliminate the complete Day and sphere-monoid records before the original free-functor getter.
theorem whole_heq (r : OrthogonalIndex) :
    HEq (FreeSourceBif.sourceFree.{u, v} r) (rawFree.{u, v} r) :=
  WholeFreeTransport.functor_heq OrthogonalDay.monoidalCategory.{u, v}
    (ColimitMonoidal.monoidalCategory d.{u, v}) rfl sphereISpace.{u, v}
    OrthogonalDay.sphereMonObj.{u, v} (LaxMonoid.monObj d.{u, v} S.{u, v} L.{u, v})
    (HEq.refl _) (Free.functor (V := PointedCGWH.{u, v}) r)

set_option maxHeartbeats 500000 in
theorem whole_eq (r : OrthogonalIndex) :
    FreeSourceBif.sourceFree.{u, v} r = rawFree.{u, v} r :=
  eq_of_heq (whole_heq r)





end OrthogonalIGeneratorProbe.NativeWholeFree
