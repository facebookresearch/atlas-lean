/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeComparisonFields
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FreeScalarKanComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.ScalarKanBoundary

/-!
# Coefficient fields of free orthogonal-spectrum smash functors

For a fixed right orthogonal spectrum `Y`, the free spectrum at an index `r`,
smashed with `Y`, is a functor of pointed coefficients. Its object is the
free enriched spectrum with that coefficient tensored with `Y`, and its map
is the free coefficient map right-whiskered by `Y`. The functor assembled
from these fields equals the evaluated curried tensor functor.
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

attribute [local instance] CanonicalSourceSmash.monoidalCategory
  CanonicalSourceSmash.symmetricCategory CanonicalSourceSmashClosed.monoidalClosed
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.EnrichedKan.hasObjectCoproduct PointedCGWH.EnrichedKan.hasRelationCoproduct
  PointedCGWH.EnrichedKan.hasBalancingCoequalizer
  SphereSmashStructure.indexCategory SphereSmashStructure.indexMonoidalCategory
  SphereSmashStructure.indexEnrichedOrdinaryCategory SphereSmashStructure.indexSymmetricCategory

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

namespace OrthogonalIGeneratorProbe.NativeEvaluatedFields

universe uEvalA vEvalA uEvalC vEvalC

private theorem evaluatedTensor_obj {A : Type uEvalA} [Category.{vEvalA} A]
    {C : Type uEvalC} [Category.{vEvalC} C] [MonoidalCategory C]
    (F : A ⥤ C) (Y : C) (K : A) :
    ((F ⋙ curriedTensor C) ⋙ (evaluation C C).obj Y).obj K = F.obj K ⊗ Y := rfl

private theorem evaluatedTensor_mapHEq {A : Type uEvalA} [Category.{vEvalA} A]
    {C : Type uEvalC} [Category.{vEvalC} C] [MonoidalCategory C]
    (F : A ⥤ C) (Y : C) {K L : A} (i : K ⟶ L) :
    HEq (((F ⋙ curriedTensor C) ⋙ (evaluation C C).obj Y).map i) (F.map i ▷ Y) := HEq.refl _

private theorem tensorMapHEq {C : Type uEvalC} [Category.{vEvalC} C] [MonoidalCategory C]
    {A A' B B' : C} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f g) (Y : C) : HEq (f ▷ Y) (g ▷ Y) := by
  cases hA
  cases hB
  exact heq_of_eq (congrArg (fun t => t ▷ Y) (eq_of_heq h))

/-- The category of native pointed orthogonal spectra with the canonical source smash
presentation. -/
abbrev Carrier := CanonicalSourceSmash.Carrier.{u, v}

/-- The original free-spectrum smash family evaluated at the fixed right spectrum `Y`. -/
def sourceOriginal (r : OrthogonalIndex) (Y : Carrier.{u, v}) :
    PointedCGWH.{u, v} ⥤ Carrier.{u, v} :=
  (FreeSourceBif.nativeFree.{u, v} r ⋙ curriedTensor Carrier.{u, v}) ⋙
    (evaluation Carrier.{u, v} Carrier.{u, v}).obj Y

/-- The literal native free spectrum at `r` with coefficient `K`, smashed on the right with `Y`. -/
def sourceObjects (r : OrthogonalIndex) (Y : Carrier.{u, v})
    (K : PointedCGWH.{u, v}) : Carrier.{u, v} :=
  Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⊗ Y

/-- The free coefficient map smashed on the right with the fixed spectrum `Y`. -/
def sourceMaps (r : OrthogonalIndex) (Y : Carrier.{u, v})
    {K L : PointedCGWH.{u, v}} (i : K ⟶ L) :
    sourceObjects r Y K ⟶ sourceObjects r Y L :=
  Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} r) i ▷ Y

theorem native_free_obj (r : OrthogonalIndex) (K : PointedCGWH.{u, v}) :
    (FreeSourceBif.nativeFree.{u, v} r).obj K =
      Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K :=
  rfl

theorem native_free_map_heq (r : OrthogonalIndex)
    {K L : PointedCGWH.{u, v}} (i : K ⟶ L) :
    HEq ((FreeSourceBif.nativeFree.{u, v} r).map i)
      (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} r) i) :=
  HEq.refl _

theorem sourceObjects_eq (r : OrthogonalIndex) (Y : Carrier.{u, v}) :
    (sourceOriginal r Y).obj = sourceObjects r Y := by
  funext K
  exact (evaluatedTensor_obj (FreeSourceBif.nativeFree r) Y K).trans
    (congrArg (fun X => X ⊗ Y) (native_free_obj r K))

theorem sourceMaps_heq (r : OrthogonalIndex) (Y : Carrier.{u, v})
    {K L : PointedCGWH.{u, v}} (i : K ⟶ L) :
    HEq ((sourceOriginal r Y).map i) (sourceMaps r Y i) := by
  exact (evaluatedTensor_mapHEq (FreeSourceBif.nativeFree r) Y i).trans
    (tensorMapHEq (native_free_obj r K) (native_free_obj r L) (native_free_map_heq r i) Y)

/-- The free-spectrum smash functor assembled from its exact native object and coefficient-map
fields. -/
def source (r : OrthogonalIndex) (Y : Carrier.{u, v}) :
    PointedCGWH.{u, v} ⥤ Carrier.{u, v} :=
  functorFromFields (sourceOriginal r Y)
    (sourceObjects r Y) (sourceObjects_eq r Y)
    (fun i => sourceMaps r Y i) (fun i => sourceMaps_heq r Y i)

theorem source_eq (r : OrthogonalIndex) (Y : Carrier.{u, v}) :
    source r Y = sourceOriginal r Y :=
  functorFromFields_eq _ _ _ _ _

theorem source_obj (r : OrthogonalIndex) (Y : Carrier.{u, v})
    (K : PointedCGWH.{u, v}) : (source r Y).obj K = sourceObjects r Y K := rfl

theorem source_map (r : OrthogonalIndex) (Y : Carrier.{u, v})
    {K L : PointedCGWH.{u, v}} (i : K ⟶ L) :
    (source r Y).map i = sourceMaps r Y i := rfl












end OrthogonalIGeneratorProbe.NativeEvaluatedFields
