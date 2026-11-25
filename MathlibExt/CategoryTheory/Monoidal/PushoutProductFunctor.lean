/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Monoidal.PushoutProduct
public import Mathlib.CategoryTheory.Monoidal.Multifunctor
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Mapping pushout-products through monoidal left adjoints

A monoidal left adjoint carries a pushout-product to the pushout-product of
the mapped arrows, canonically up to an isomorphism in the arrow category.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory

namespace CategoryTheory.Functor

/-- A monoidal left adjoint carries a pushout-product to the pushout-product
of the mapped arrows. -/
noncomputable def mapArrowPushoutProductIso
    {C : Type u₁} [Category.{v₁} C]
    [MonoidalCategory C] [HasPushouts C]
    {D : Type u₂} [Category.{v₂} D]
    [MonoidalCategory D] [HasPushouts D]
    (F : C ⥤ D) [F.IsLeftAdjoint] [F.Monoidal]
    {A B K L : C} (i : A ⟶ B) (j : K ⟶ L) :
    F.mapArrow.obj (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j) ≅
      CategoryTheory.Arrow.mk (F.map i) □ CategoryTheory.Arrow.mk (F.map j) := by
  let sq := PushoutObjObj.ofHasPushout (curriedTensor C) i j
  let mappedSq : (curriedTensorPost F).PushoutObjObj i j :=
    { pt := F.obj sq.pt
      inl := F.map sq.inl
      inr := F.map sq.inr
      isPushout := F.map_isPushout sq.isPushout
      ι := F.map sq.ι
      inl_ι := by
        rw [← F.map_comp, sq.inl_ι]
        rfl
      inr_ι := by
        rw [← F.map_comp, sq.inr_ι]
        rfl }
  let targetSq := mappedSq.ofNatIso
    (Functor.curriedTensorPreIsoPost F).symm
  let standardSq := PushoutObjObj.ofHasPushout
    (curriedTensorPre F) i j
  let eLeft := targetSq.isPushout.isoIsPushout _ _ standardSq.isPushout
  have hι : eLeft.hom ≫ standardSq.ι = targetSq.ι := by
    apply targetSq.isPushout.hom_ext
    · rw [targetSq.isPushout.inl_isoIsPushout_hom_assoc
          _ _ standardSq.isPushout]
      rw [standardSq.inl_ι]
      exact targetSq.inl_ι.symm
    · rw [targetSq.isPushout.inr_isoIsPushout_hom_assoc
          _ _ standardSq.isPushout]
      rw [standardSq.inr_ι]
      exact targetSq.inr_ι.symm
  change CategoryTheory.Arrow.mk (F.map sq.ι) ≅
    CategoryTheory.Arrow.mk standardSq.ι
  refine CategoryTheory.Arrow.isoMk eLeft
    (Functor.Monoidal.μIso F B L).symm ?_
  change eLeft.hom ≫ standardSq.ι =
    F.map sq.ι ≫
      ((Functor.curriedTensorPreIsoPost F).symm.hom.app B).app L
  exact hι

end CategoryTheory.Functor
