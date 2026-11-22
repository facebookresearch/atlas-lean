/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.TranslatedOutputCoefficients
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration

/-!
# Native outputs of orthogonal free-source mapping

For a native orthogonal diagram, the internal module-Hom output with free source at r and
coefficient K is isomorphic to the module of the r-shifted cotensor by K. The comparison is
constructed from the module-stage isomorphism and is natural under precomposition by
coefficient maps.
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

namespace OrthogonalIGeneratorProbe.NativeCoefficient

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

/-- Isomorphisms from a free-source module-Hom output to the module of the native right-shifted
cotensor. -/
def OutputIsoType (r : OrthogonalIndex) (K : PointedCGWH.{u, v}) (Z : NativeDiagram.{u, v}) :=
  (ModuleMappingR.functor d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    (FreeSource.freeAt r K)).obj (toModule.{u, v} Z) ≅
      toModule.{u, v} (FreeSourceAction.NativeModule.shiftedCotensor r K Z)

/-- The free-source output isomorphism induced by the original literal module-stage comparison. -/
def outputIso (r : OrthogonalIndex) (K : PointedCGWH.{u, v}) (Z : NativeDiagram.{u, v}) :
    OutputIsoType r K Z :=
  FunctionIteration.Internal.functorOutputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    (FreeSourceAction.LiteralModuleStage.moduleIso r K Z)

theorem outputIso_coefficient (r : OrthogonalIndex) {K K' : PointedCGWH.{u, v}}
    (i : K ⟶ K') (Z : NativeDiagram.{u, v}) :
    moduleSourceMap d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
      (freeMap d.{u, v} S.{u, v} L.{u, v}
        ((Free.functor (V := PointedCGWH.{u, v}) r).map i))
      (toModule.{u, v} Z) ≫
        (outputIso r K Z).hom =
      (outputIso r K' Z).hom ≫ toModuleFunctor.map
        (cotensorScalarMap i ((RightShift.shift r).obj Z)) := by
  apply Coefficient.outputCoefficient d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r i
    (toModule.{u, v} Z) (toModule.{u, v} (FreeSourceAction.NativeModule.shiftedCotensor r K Z))
    (toModule.{u, v} (FreeSourceAction.NativeModule.shiftedCotensor r K' Z))
    (outputIso r K Z) (outputIso r K' Z)
    (toModuleFunctor.map (cotensorScalarMap i ((RightShift.shift r).obj Z)))
    (FreeSourceAction.LiteralModuleStage.target_objects r K Z)
    (FreeSourceAction.LiteralModuleStage.target_objects r K' Z)
  · intro c
    exact FunctionIteration.Internal.outputIso_component d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
      r K (toModule.{u, v} Z)
      (toModule.{u, v} (FreeSourceAction.NativeModule.shiftedCotensor r K Z))
      (FreeSourceAction.LiteralModuleStage.carrierIso r K Z)
      (FreeSourceAction.LiteralModuleStage.target_objects r K Z)
      (FreeSourceAction.LiteralModuleStage.carrier_component r K Z)
      (FreeSourceAction.LiteralModuleStage.target_action r K Z) c
  · intro c
    exact FunctionIteration.Internal.outputIso_component d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
      r K' (toModule.{u, v} Z)
      (toModule.{u, v} (FreeSourceAction.NativeModule.shiftedCotensor r K' Z))
      (FreeSourceAction.LiteralModuleStage.carrierIso r K' Z)
      (FreeSourceAction.LiteralModuleStage.target_objects r K' Z)
      (FreeSourceAction.LiteralModuleStage.carrier_component r K' Z)
      (FreeSourceAction.LiteralModuleStage.target_action r K' Z) c
  · intro c
    change component (SphereModuleMappingEnd.moduleMap d.{u, v} S.{u, v} L.{u, v}
        (toModuleFunctor.map (cotensorScalarMap i ((RightShift.shift r).obj Z)))) c ≫
        𝟙 _ = 𝟙 _ ≫ (MonoidalClosed.pre i).app _
    rw [Category.comp_id, Category.id_comp]
    exact (toModuleMap_component.{u, v} (cotensorScalarMap i ((RightShift.shift r).obj Z)) c).trans
      (cotensorScalarMap_component i ((RightShift.shift r).obj Z)
        (OrthogonalOperatorIndex.ofIndex.{u, v} c))




end OrthogonalIGeneratorProbe.NativeCoefficient
