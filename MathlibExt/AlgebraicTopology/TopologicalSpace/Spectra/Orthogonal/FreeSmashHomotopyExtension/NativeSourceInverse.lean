/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeSourceMappingComparison
import MathlibExt.CategoryTheory.Equivalence.FunctorFamily
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FreeMappingFields
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeFreeFunctor
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NormalizedFreeMapping
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NormalizedFreeCoefficients
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeTargetNaturality
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration

/-!
# Inverse module transport and free mapping objects

Retains the module/operator equivalence and its complete inverse functor. Constructs free-module
mapping-object comparisons natural in both the coefficient parameter and the target operator
diagram.
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

namespace OrthogonalIGeneratorProbe.NativeWholeSource

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

/-- The original source equivalence with its inverse replaced by the equal explicit module
functor. -/
def sourceEquivalence : Module d.{u, v} S.{u, v} L.{u, v} ≌ NativeDiagram.{u, v} :=
  NativeSourceBoundary.sourceEquivalence.{u, v}.changeInverse
    (eqToIso NativeSourceBoundary.inverse_eq.{u, v})

theorem whole_eq : sourceEquivalence.{u, v} = NativeSourceBoundary.sourceEquivalence.{u, v} := by
  have h (E : Module d.{u, v} S.{u, v} L.{u, v} ≌ NativeDiagram.{u, v})
      (Q : NativeDiagram.{u, v} ⥤ Module d.{u, v} S.{u, v} L.{u, v})
      (hQ : E.inverse = Q) : E.changeInverse (eqToIso hQ) = E := by
    cases hQ
    change E.changeInverse (Iso.refl _) = E
    cat_disch
  exact h _ _ NativeSourceBoundary.inverse_eq.{u, v}

theorem inverse_eq : sourceEquivalence.{u, v}.inverse = NativeSourceBoundary.sourceFunctor.{u, v} := rfl

/-- The free-source output comparison written with the exact inverse of the original source
equivalence. -/
def element (r : OrthogonalIndex) (K : PointedCGWH.{u, v}ᵒᵖ) (Z : NativeDiagram.{u, v}) :
    (ModuleMappingR.functor d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
      (FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r K.unop)).obj
        (sourceEquivalence.{u, v}.inverse.obj Z) ≅
      sourceEquivalence.{u, v}.inverse.obj
        ((NativeTargetBoundary.objectFunction.{u, v} r K).obj Z) :=
  NativeSourceBoundary.element r K Z

theorem target_square (r : OrthogonalIndex) (K : PointedCGWH.{u, v}ᵒᵖ)
    {Z Z' : NativeDiagram.{u, v}} (f : Z ⟶ Z') :
    (ModuleMappingR.functor d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
      (FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r K.unop)).map
        (sourceEquivalence.{u, v}.inverse.map f) ≫ (element r K Z').hom =
      (element r K Z).hom ≫ sourceEquivalence.{u, v}.inverse.map
        ((NativeTargetBoundary.objectFunction.{u, v} r K).map f) :=
  NativeSourceBoundary.target_square r K f

theorem parameter_square (r : OrthogonalIndex) {K K' : PointedCGWH.{u, v}ᵒᵖ}
    (i : K ⟶ K') (Z : NativeDiagram.{u, v}) :
    ModuleMappingR.moduleSourceMap d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
        (freeMap d.{u, v} S.{u, v} L.{u, v} ((Free.functor r).map i.unop))
        (sourceEquivalence.{u, v}.inverse.obj Z) ≫ (element r K' Z).hom =
      (element r K Z).hom ≫ sourceEquivalence.{u, v}.inverse.map
        ((NativeSourceBoundary.parameterMap r i).app Z) :=
  NativeSourceBoundary.parameter_square r i Z








end OrthogonalIGeneratorProbe.NativeWholeSource
