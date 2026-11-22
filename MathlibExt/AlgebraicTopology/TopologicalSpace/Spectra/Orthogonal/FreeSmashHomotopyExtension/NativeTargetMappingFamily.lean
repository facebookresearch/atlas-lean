/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeMappingElement
import MathlibExt.CategoryTheory.Equivalence.FunctorFamily
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FreeMappingFields
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeFreeFunctor
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NormalizedFreeMapping
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NormalizedFreeCoefficients
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeTargetNaturality
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration

/-!
# Right-shifted cotensor families for orthogonal spectra

Forms the contravariant coefficient family that first right-shifts an orthogonal
spectrum and then cotensors it. An explicit object presentation is proved equal to the
same full functor, and coefficient maps remain the whiskered scalar-cotensor maps.
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

universe uCopyA vCopyA uCopyD vCopyD

private theorem copyObject_eq {A : Type uCopyA} [Category.{vCopyA} A]
    {D : Type uCopyD} [Category.{vCopyD} D] (F : A ⥤ D) (o : A → D) (h : F.obj = o) :
    F.copyObj o (fun X => eqToIso (congrFun h X)) = F := by
  cases h
  exact CategoryTheory.Functor.ext_of_iso
    (F.isoCopyObj F.obj (fun X => eqToIso (congrFun (rfl : F.obj = F.obj) X))).symm
    (fun _ => rfl) (fun _ => rfl)

private theorem copyObject_map_heq {A : Type uCopyA} [Category.{vCopyA} A]
    {D : Type uCopyD} [Category.{vCopyD} D] (F : A ⥤ D) (o : A → D) (h : F.obj = o)
    {X Y : A} (f : X ⟶ Y) :
    HEq ((F.copyObj o (fun Z => eqToIso (congrFun h Z))).map f) (F.map f) := by
  cases h
  exact heq_of_eq (by simp [Functor.copyObj])

namespace OrthogonalIGeneratorProbe.NativeTargetBoundary

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

/-- The contravariant cotensor family whiskered on the left by the original right-shift functor. -/
def rawFamily (r : OrthogonalIndex) : PointedCGWH.{u, v}ᵒᵖ ⥤
    (NativeDiagram.{u, v} ⥤ NativeDiagram.{u, v}) :=
  ScalarLeibniz.cotensorBifunctor ⋙
    (Functor.whiskeringLeft NativeDiagram.{u, v} NativeDiagram.{u, v}
      NativeDiagram.{u, v}).obj (RightShift.shift r)

/-- The native endofunctor that first right-shifts by `r` and then cotensors with `K.unop`. -/
def objectFunction (r : OrthogonalIndex) (K : PointedCGWH.{u, v}ᵒᵖ) :
    NativeDiagram.{u, v} ⥤ NativeDiagram.{u, v} :=
  RightShift.shift r ⋙ cotensor K.unop

theorem objectFunction_eq (r : OrthogonalIndex) :
    (rawFamily.{u, v} r).obj = objectFunction.{u, v} r := by
  funext K
  rfl

/-- The right-shifted cotensor family with its object field replaced by the equal explicit
composite. -/
def family (r : OrthogonalIndex) :=
  (rawFamily.{u, v} r).copyObj (objectFunction.{u, v} r)
    (fun K => eqToIso (congrFun (objectFunction_eq.{u, v} r) K))

theorem whole_eq (r : OrthogonalIndex) : family.{u, v} r = rawFamily.{u, v} r :=
  copyObject_eq (rawFamily.{u, v} r) (objectFunction.{u, v} r) (objectFunction_eq.{u, v} r)

theorem map_heq (r : OrthogonalIndex) {K K' : PointedCGWH.{u, v}ᵒᵖ} (i : K ⟶ K') :
    HEq ((family.{u, v} r).map i)
      (Functor.whiskerLeft (RightShift.shift r) (ScalarLeibniz.cotensorBifunctor.map i)) :=
  (copyObject_map_heq (rawFamily.{u, v} r)
    (objectFunction.{u, v} r) (objectFunction_eq.{u, v} r) i).trans (HEq.refl _)

theorem map_eq (r : OrthogonalIndex) {K K' : PointedCGWH.{u, v}ᵒᵖ} (i : K ⟶ K') :
    (family.{u, v} r).map i =
      Functor.whiskerLeft (RightShift.shift r) (ScalarLeibniz.cotensorBifunctor.map i) :=
  eq_of_heq (map_heq r i)








end OrthogonalIGeneratorProbe.NativeTargetBoundary
