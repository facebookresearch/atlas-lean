/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.Presentable.PresheafMonomorphismFiltration

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Subfunctor CategoryTheory.Limits
open scoped PresheafMonomorphismFiltration

variable {E : Type u} [SmallCategory E] {A B : Eᵒᵖ ⥤ Type u}

example (f : A ⟶ B) [Mono f] :
    (MorphismProperty.boundedPresheafMonomorphisms E).pushouts.TransfiniteCompositionOfShape
      (Set.Iic (⊤ : PresheafSectionIndex B)) f :=
  presheafMonomorphismFiltration f

example (f : A ⟶ B) : presheafMonoPrefix f ⊥ = range f :=
  presheafMonoPrefix_bot f

example (f : A ⟶ B) : presheafMonoPrefix f ⊤ = ⊤ :=
  presheafMonoPrefix_top f

example (f : A ⟶ B) (j : PresheafSectionIndex B) (hj : ¬ IsMax j) :
    presheafMonoPrefix f (Order.succ j) =
      presheafMonoPrefix f j ⊔ presheafSectionSeed B j :=
  presheafMonoPrefix_succ f j hj

example (f : A ⟶ B) (j : PresheafSectionIndex B) (hj : Order.IsSuccLimit j) :
    presheafMonoPrefix f j = ⨆ k : Set.Iio j, presheafMonoPrefix f k.1 :=
  presheafMonoPrefix_limit f j hj

example (f : A ⟶ B) (j : PresheafSectionIndex B) (hj : ¬ IsMax j) :
    Cardinal.mk (presheafMonoCell f j).left.Elements ≤
        max Cardinal.aleph0 (Cardinal.mk (Arrow E)) ∧
      Cardinal.mk (presheafMonoCell f j).right.Elements ≤
        max Cardinal.aleph0 (Cardinal.mk (Arrow E)) :=
  (presheafMonoCell_bounded f j hj).2

example (f : A ⟶ B) (j : PresheafSectionIndex B) (hj : ¬ IsMax j) :
    IsPushout (presheafMonoCell f j).hom
      (homOfLe (show presheafMonoPrefix f j ⊓ presheafSectionSeed B j ≤
        presheafMonoPrefix f j from inf_le_left))
      (homOfLe (presheafSectionSeed_le_succ f j hj))
      (homOfLe (presheafMonoPrefix_mono f (Order.le_succ j))) :=
  presheafMonoSuccessor_isPushout f j hj

example (f : A ⟶ B) [Mono f] (j : Set.Iic (⊤ : PresheafSectionIndex B)) :
    (presheafMonomorphismFiltration f).F.obj j = (presheafMonoPrefix f j.1).toFunctor := rfl

example (f : A ⟶ B) [Mono f] (j k : Set.Iic (⊤ : PresheafSectionIndex B)) (h : j ≤ k) :
    (presheafMonomorphismFiltration f).F.map (homOfLE h) =
      homOfLe (presheafMonoPrefix_mono f (show j.1 ≤ k.1 from h)) := rfl

example (f : A ⟶ B) [Mono f] :
    (presheafMonomorphismFiltration f).isoBot.inv ≫
      (presheafMonomorphismFiltration f).incl.app ⊥ = f :=
  (presheafMonomorphismFiltration f).fac

example (f : A ⟶ B) [Mono f] :
    (presheafMonoPrefixArrowIso f).hom.left = inv (toRange f) := by
  simp [presheafMonoPrefixArrowIso]

example (f : A ⟶ B) [Mono f] :
    (presheafMonoPrefixArrowIso f).hom.right = (presheafMonoPrefix f ⊤).ι := by
  simp [presheafMonoPrefixArrowIso]

example (s : B.Elements) (hs : IsMax s) :
    Order.succ (s : PresheafSectionIndex B) = ⊤ :=
  WithTop.succ_coe_of_isMax hs

example [IsEmpty B.Elements] : (⊥ : PresheafSectionIndex B) = ⊤ :=
  WithTop.eq_top_of_isEmpty

example (f : A ⟶ B) [Mono f] :
    IsColimit (Cocone.mk B (presheafMonomorphismFiltration f).incl) :=
  (presheafMonomorphismFiltration f).isColimit
