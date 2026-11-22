/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeSourceMappingComparison
import Mathlib.CategoryTheory.EqToHom
import MathlibExt.CategoryTheory.Equivalence.FunctorFamily
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FreeMappingFields
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeFreeFunctor
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NormalizedFreeMapping
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NormalizedFreeCoefficients
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeTargetNaturality
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration

/-!
# Orthogonal mapping families and coefficient maps

At a fixed orthogonal index, the shifted-cotensor family is assembled from
its explicit native objects and contravariant coefficient maps. Equality
of the object fields and heterogeneous equality of the maps inherit the
functoriality laws from the given family. The resulting whole family agrees
with `NativeTargetBoundary.rawFamily`, and its coefficient maps are
`NativeSourceBoundary.parameterMap`.
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

universe uAuxA vAuxA uAuxD vAuxD

private def functorFromFields {A : Type uAuxA} [Category.{vAuxA} A]
    {D : Type uAuxD} [Category.{vAuxD} D]
    (F : A ⥤ D) (o : A → D) (ho : F.obj = o)
    (m : ∀ {X Y : A}, (X ⟶ Y) → (o X ⟶ o Y))
    (hm : ∀ {X Y : A} (f : X ⟶ Y), HEq (F.map f) (m f)) : A ⥤ D where
  obj := o
  map := m
  map_id X := by
    cases ho
    exact (eq_of_heq (hm (𝟙 X))).symm.trans (F.map_id X)
  map_comp f g := by
    cases ho
    have hf := eq_of_heq (hm f)
    have hg := eq_of_heq (hm g)
    have hfg := eq_of_heq (hm (f ≫ g))
    exact hfg.symm.trans ((F.map_comp f g).trans (by rw [hf, hg]))

private theorem functorFromFields_eq {A : Type uAuxA} [Category.{vAuxA} A]
    {D : Type uAuxD} [Category.{vAuxD} D]
    (F : A ⥤ D) (o : A → D) (ho : F.obj = o)
    (m : ∀ {X Y : A}, (X ⟶ Y) → (o X ⟶ o Y))
    (hm : ∀ {X Y : A} (f : X ⟶ Y), HEq (F.map f) (m f)) :
    functorFromFields F o ho m hm = F := by
  cases ho
  exact Functor.hext (fun _ => rfl) (fun _ _ f => (hm f).symm)

namespace OrthogonalIGeneratorProbe.FixedTarget

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

/-- The shifted-cotensor family assembled from its explicit native objects and contravariant
coefficient maps. -/
def family (r : OrthogonalIndex) :=
  functorFromFields (NativeTargetBoundary.family.{u, v} r)
    (NativeTargetBoundary.objectFunction.{u, v} r) (NativeSourceBoundary.targetObject_eq r)
    (fun i => NativeSourceBoundary.parameterMap r i)
    (fun i => NativeSourceBoundary.targetMap_heq r i)

theorem whole_eq (r : OrthogonalIndex) : family.{u, v} r = NativeTargetBoundary.rawFamily.{u, v} r :=
  (functorFromFields_eq _ _ _ _ _).trans (NativeTargetBoundary.whole_eq r)

theorem map_eq (r : OrthogonalIndex) {K K' : PointedCGWH.{u, v}ᵒᵖ} (i : K ⟶ K') :
    (family.{u, v} r).map i = NativeSourceBoundary.parameterMap r i := rfl





end OrthogonalIGeneratorProbe.FixedTarget
