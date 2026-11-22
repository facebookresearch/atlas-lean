/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.MorphismProperty.Basic
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeComparisonFields
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FreeScalarKanComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.ScalarKanBoundary

/-!
# Object and morphism fields of the scalar Kan target

Evaluates the scalar-tensor and left Kan family at a fixed orthogonal spectrum. The reconstructed coefficient functor has exactly the objects and maps obtained by left Kan extension of the native scalar tensor, and equals the original evaluated family.
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

namespace OrthogonalIGeneratorProbe.NativeEvaluatedTarget

/-- The category of native pointed orthogonal spectra with the canonical source smash
presentation. -/
abbrev Carrier := CanonicalSourceSmash.Carrier.{u, v}

/-- The original scalar-tensor and left Kan family evaluated at the fixed spectrum `Y`. -/
def targetOriginal (r : OrthogonalIndex) (Y : Carrier.{u, v}) :
    PointedCGWH.{u, v} ⥤ Carrier.{u, v} :=
  FinalLeftMate.scalarKanFamily.{u, v} r ⋙ (evaluation Carrier.{u, v} Carrier.{u, v}).obj Y

/-- Left Kan extension along the right-shift index of the scalar tensor of `K` with `Y`. -/
def targetObjects (r : OrthogonalIndex) (Y : Carrier.{u, v})
    (K : PointedCGWH.{u, v}) : Carrier.{u, v} :=
  (leftKan (RightShift.indexShift.{u, v} r)).obj (tensorLeftObject K Y)

/-- The scalar coefficient map on `Y` sent through left Kan extension along the original
right-shift index. -/
def targetMaps (r : OrthogonalIndex) (Y : Carrier.{u, v})
    {K L : PointedCGWH.{u, v}} (i : K ⟶ L) :
    targetObjects r Y K ⟶ targetObjects r Y L :=
  (leftKan (RightShift.indexShift.{u, v} r)).map (scalarTensorMap i Y)

theorem targetObjects_eq (r : OrthogonalIndex) (Y : Carrier.{u, v}) :
    (targetOriginal r Y).obj = targetObjects r Y := rfl

theorem targetMaps_heq (r : OrthogonalIndex) (Y : Carrier.{u, v})
    {K L : PointedCGWH.{u, v}} (i : K ⟶ L) :
    HEq ((targetOriginal r Y).map i) (targetMaps r Y i) :=
  heq_of_eq (FinalGetters.kan_map r i Y)

/-- The scalar Kan functor assembled from its exact native object and coefficient-map fields. -/
def target (r : OrthogonalIndex) (Y : Carrier.{u, v}) :
    PointedCGWH.{u, v} ⥤ Carrier.{u, v} :=
  functorFromFields (targetOriginal r Y)
    (targetObjects r Y) (targetObjects_eq r Y)
    (fun i => targetMaps r Y i) (fun i => targetMaps_heq r Y i)

theorem target_eq (r : OrthogonalIndex) (Y : Carrier.{u, v}) :
    target r Y = targetOriginal r Y :=
  functorFromFields_eq _ _ _ _ _

theorem target_obj (r : OrthogonalIndex) (Y : Carrier.{u, v})
    (K : PointedCGWH.{u, v}) : (target r Y).obj K = targetObjects r Y K := rfl

theorem target_map (r : OrthogonalIndex) (Y : Carrier.{u, v})
    {K L : PointedCGWH.{u, v}} (i : K ⟶ L) :
    (target r Y).map i = targetMaps r Y i := rfl











end OrthogonalIGeneratorProbe.NativeEvaluatedTarget
