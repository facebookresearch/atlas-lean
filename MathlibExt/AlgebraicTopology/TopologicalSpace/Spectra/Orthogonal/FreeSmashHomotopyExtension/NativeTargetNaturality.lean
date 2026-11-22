/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeOutputCoefficient
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration

/-!
# Target naturality of free orthogonal mapping

The free-source mapping comparison is natural in every native target-spectrum morphism. Its module-side mapping map corresponds to the map of the right-shifted cotensor under the same presentation functor.
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

namespace OrthogonalIGeneratorProbe.NativeTarget

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

theorem outputIso_naturality (r : OrthogonalIndex) (K : PointedCGWH.{u, v})
    {Z Z' : NativeDiagram.{u, v}} (f : Z ⟶ Z') :
    (ModuleMappingR.functor d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
        (FreeSource.freeAt r K)).map (toModuleFunctor.map f) ≫
        (NativeCoefficient.outputIso r K Z').hom =
      (NativeCoefficient.outputIso r K Z).hom ≫
        toModuleFunctor.map ((RightShift.shift r ⋙ cotensor K).map f) := by
  apply FunctionIteration.Internal.output_naturality
    d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r K
    (toModuleFunctor.map f)
    (toModuleFunctor.map ((RightShift.shift r ⋙ cotensor K).map f))
    (NativeCoefficient.outputIso r K Z) (NativeCoefficient.outputIso r K Z')
    (FreeSourceAction.LiteralModuleStage.target_objects r K Z)
    (FreeSourceAction.LiteralModuleStage.target_objects r K Z')
  · intro c
    exact FunctionIteration.Internal.outputIso_component d.{u, v} b.{u, v}
      S.{u, v} L.{u, v} B.{u, v} r K (toModule.{u, v} Z)
      (toModule.{u, v} (FreeSourceAction.NativeModule.shiftedCotensor r K Z))
      (FreeSourceAction.LiteralModuleStage.carrierIso r K Z)
      (FreeSourceAction.LiteralModuleStage.target_objects r K Z)
      (FreeSourceAction.LiteralModuleStage.carrier_component r K Z)
      (FreeSourceAction.LiteralModuleStage.target_action r K Z) c
  · intro c
    exact FunctionIteration.Internal.outputIso_component d.{u, v} b.{u, v}
      S.{u, v} L.{u, v} B.{u, v} r K (toModule.{u, v} Z')
      (toModule.{u, v} (FreeSourceAction.NativeModule.shiftedCotensor r K Z'))
      (FreeSourceAction.LiteralModuleStage.carrierIso r K Z')
      (FreeSourceAction.LiteralModuleStage.target_objects r K Z')
      (FreeSourceAction.LiteralModuleStage.carrier_component r K Z')
      (FreeSourceAction.LiteralModuleStage.target_action r K Z') c
  · intro c
    have h₁ := toModuleMap_component.{u, v} ((RightShift.shift r ⋙ cotensor K).map f) c
    have h₂ := cotensorMap_component K ((RightShift.shift r).map f)
      (OrthogonalOperatorIndex.ofIndex.{u, v} c)
    have h₃ := congrArg (ihom K).map (RightShift.shift_map_component r c f)
    have h₄ := congrArg (ihom K).map (toModuleMap_component.{u, v} f (c + r))
    exact (Category.comp_id _).trans
      ((h₁.trans (h₂.trans (h₃.trans h₄.symm))).trans (Category.id_comp _).symm)



end OrthogonalIGeneratorProbe.NativeTarget
