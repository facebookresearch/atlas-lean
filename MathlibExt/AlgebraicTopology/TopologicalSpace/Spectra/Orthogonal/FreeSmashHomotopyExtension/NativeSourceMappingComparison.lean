/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeTargetMappingFamily
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.OriginalNormalizedMappingEquality
import MathlibExt.CategoryTheory.Equivalence.FunctorFamily
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FreeMappingFields
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeFreeFunctor
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NormalizedFreeMapping
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NormalizedFreeCoefficients
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeTargetNaturality
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration

/-!
# Source and coefficient naturality of free orthogonal mapping

Compares the module mapping object from a free orthogonal spectrum with the module presentation of a right-shifted native cotensor. The comparison is natural in the target spectrum and contravariant coefficient, using the same module/operator equivalence and source-mapping maps.
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

namespace OrthogonalIGeneratorProbe.NativeSourceBoundary

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

/-- The original equivalence from orthogonal sphere modules to native operator diagrams. -/
def sourceEquivalence : Module d.{u, v} S.{u, v} L.{u, v} ≌ NativeDiagram.{u, v} :=
  equivalence.{u, v}.symm

theorem sourceEquivalence_heq : HEq sourceEquivalence.{u, v} equivalence.{u, v}.symm :=
  HEq.refl _

/-- The original functor taking a native operator diagram to its orthogonal sphere module. -/
def sourceFunctor : NativeDiagram.{u, v} ⥤ Module d.{u, v} S.{u, v} L.{u, v} :=
  toModuleFunctor.{u, v}

theorem inverse_eq : sourceEquivalence.{u, v}.inverse = sourceFunctor.{u, v} := rfl

/-- The contravariant cotensor coefficient map whiskered by the original right-shift functor. -/
def parameterMap (r : OrthogonalIndex) {K K' : PointedCGWH.{u, v}ᵒᵖ} (i : K ⟶ K') :
    NativeTargetBoundary.objectFunction.{u, v} r K ⟶ NativeTargetBoundary.objectFunction.{u, v} r K' :=
  Functor.whiskerLeft (RightShift.shift r) (ScalarLeibniz.cotensorBifunctor.map i)

theorem targetObject_eq (r : OrthogonalIndex) :
    (NativeTargetBoundary.family.{u, v} r).obj = NativeTargetBoundary.objectFunction.{u, v} r := rfl

theorem targetMap_heq (r : OrthogonalIndex) {K K' : PointedCGWH.{u, v}ᵒᵖ} (i : K ⟶ K') :
    HEq ((NativeTargetBoundary.family.{u, v} r).map i) (parameterMap r i) :=
  NativeTargetBoundary.map_heq r i

/-- The free-source module-Hom output compared with the module of the shifted native cotensor. -/
def element (r : OrthogonalIndex) (K : PointedCGWH.{u, v}ᵒᵖ) (Z : NativeDiagram.{u, v}) :
    (ModuleMappingR.functor d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
      (FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r K.unop)).obj (sourceFunctor.{u, v}.obj Z) ≅
        sourceFunctor.{u, v}.obj ((NativeTargetBoundary.objectFunction.{u, v} r K).obj Z) :=
  NativeCoefficient.outputIso r K.unop Z

theorem target_square (r : OrthogonalIndex) (K : PointedCGWH.{u, v}ᵒᵖ)
    {Z Z' : NativeDiagram.{u, v}} (f : Z ⟶ Z') :
    (ModuleMappingR.functor d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
      (FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r K.unop)).map (sourceFunctor.{u, v}.map f) ≫
        (element r K Z').hom = (element r K Z).hom ≫
          sourceFunctor.{u, v}.map ((NativeTargetBoundary.objectFunction.{u, v} r K).map f) :=
  NativeTarget.outputIso_naturality r K.unop f

theorem parameter_square (r : OrthogonalIndex) {K K' : PointedCGWH.{u, v}ᵒᵖ}
    (i : K ⟶ K') (Z : NativeDiagram.{u, v}) :
    ModuleMappingR.moduleSourceMap d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
        (freeMap d.{u, v} S.{u, v} L.{u, v} ((Free.functor r).map i.unop))
        (sourceFunctor.{u, v}.obj Z) ≫ (element r K' Z).hom =
      (element r K Z).hom ≫ sourceFunctor.{u, v}.map ((parameterMap r i).app Z) :=
  NativeCoefficient.outputIso_coefficient r i.unop Z












end OrthogonalIGeneratorProbe.NativeSourceBoundary
