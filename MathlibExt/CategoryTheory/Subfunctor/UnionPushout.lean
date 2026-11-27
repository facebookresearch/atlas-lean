/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Limits.Types.Multicoequalizer
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-!
# Literal intersection–union pushouts of subfunctors

The pointwise bicartesian square of subsets gives the original pushout of
subfunctors. The chosen-pushout comparison retains its four injection laws
and both naturality directions for maps of the original squares.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory.Limits

namespace CategoryTheory.Subfunctor

variable {J : Type u} [Category.{v} J] {F F' : J ⥤ Type w}

/-- The native intersection/union inclusions form a pushout on the original
functor site, without a size or model assumption. -/
theorem isPushout_inf_sup (U V : Subfunctor F) :
    IsPushout (homOfLe (show U ⊓ V ≤ V from inf_le_right))
      (homOfLe (show U ⊓ V ≤ U from inf_le_left))
      (homOfLe (show V ≤ U ⊔ V from le_sup_right))
      (homOfLe (show U ≤ U ⊔ V from le_sup_left)) := by
  apply IsPushout.of_forall_isPushout_app
  intro j
  exact Types.isPushout_of_bicartSq
    (show Lattice.BicartSq ((U ⊓ V).obj j) (V.obj j) (U.obj j) ((U ⊔ V).obj j) from
      ⟨sup_comm _ _, inf_comm _ _⟩)

/-- The selected pushout of the original span is the literal union. -/
def unionPushoutIso (U V : Subfunctor F) :
    pushout (homOfLe (show U ⊓ V ≤ V from inf_le_right))
      (homOfLe (show U ⊓ V ≤ U from inf_le_left)) ≅ (U ⊔ V).toFunctor :=
  (isPushout_inf_sup U V).isoPushout.symm

/-- Both hom and inverse injection equations use the same selected comparison. -/
theorem unionPushoutIso_legs (U V : Subfunctor F) :
    (pushout.inl (homOfLe (show U ⊓ V ≤ V from inf_le_right))
        (homOfLe (show U ⊓ V ≤ U from inf_le_left)) ≫ (unionPushoutIso U V).hom =
      homOfLe (show V ≤ U ⊔ V from le_sup_right)) ∧
    (pushout.inr (homOfLe (show U ⊓ V ≤ V from inf_le_right))
        (homOfLe (show U ⊓ V ≤ U from inf_le_left)) ≫ (unionPushoutIso U V).hom =
      homOfLe (show U ≤ U ⊔ V from le_sup_left)) ∧
    (homOfLe (show V ≤ U ⊔ V from le_sup_right) ≫ (unionPushoutIso U V).inv =
      pushout.inl (homOfLe (show U ⊓ V ≤ V from inf_le_right))
        (homOfLe (show U ⊓ V ≤ U from inf_le_left))) ∧
    (homOfLe (show U ≤ U ⊔ V from le_sup_left) ≫ (unionPushoutIso U V).inv =
      pushout.inr (homOfLe (show U ⊓ V ≤ V from inf_le_right))
        (homOfLe (show U ⊓ V ≤ U from inf_le_left))) :=
  ⟨(isPushout_inf_sup U V).inl_isoPushout_inv,
    (isPushout_inf_sup U V).inr_isoPushout_inv,
    (isPushout_inf_sup U V).inl_isoPushout_hom,
    (isPushout_inf_sup U V).inr_isoPushout_hom⟩

/-- The same hom and inverse comparisons are natural for a map between the
original squares. The four presheaf objects may all change. -/
theorem unionPushoutIso_naturality (U V : Subfunctor F) (U' V' : Subfunctor F')
    (a : V.toFunctor ⟶ V'.toFunctor) (b : U.toFunctor ⟶ U'.toFunctor)
    (c : (U ⊓ V).toFunctor ⟶ (U' ⊓ V').toFunctor)
    (d : (U ⊔ V).toFunctor ⟶ (U' ⊔ V').toFunctor)
    (h₁ : homOfLe (show U ⊓ V ≤ V from inf_le_right) ≫ a =
      c ≫ homOfLe (show U' ⊓ V' ≤ V' from inf_le_right))
    (h₂ : homOfLe (show U ⊓ V ≤ U from inf_le_left) ≫ b =
      c ≫ homOfLe (show U' ⊓ V' ≤ U' from inf_le_left))
    (h₃ : homOfLe (show V ≤ U ⊔ V from le_sup_right) ≫ d =
      a ≫ homOfLe (show V' ≤ U' ⊔ V' from le_sup_right))
    (h₄ : homOfLe (show U ≤ U ⊔ V from le_sup_left) ≫ d =
      b ≫ homOfLe (show U' ≤ U' ⊔ V' from le_sup_left)) :
    let m := pushout.map
      (homOfLe (show U ⊓ V ≤ V from inf_le_right))
      (homOfLe (show U ⊓ V ≤ U from inf_le_left))
      (homOfLe (show U' ⊓ V' ≤ V' from inf_le_right))
      (homOfLe (show U' ⊓ V' ≤ U' from inf_le_left)) a b c h₁ h₂
    (m ≫ (unionPushoutIso U' V').hom = (unionPushoutIso U V).hom ≫ d) ∧
      (d ≫ (unionPushoutIso U' V').inv = (unionPushoutIso U V).inv ≫ m) := by
  dsimp only
  have h : pushout.map
      (homOfLe (show U ⊓ V ≤ V from inf_le_right))
      (homOfLe (show U ⊓ V ≤ U from inf_le_left))
      (homOfLe (show U' ⊓ V' ≤ V' from inf_le_right))
      (homOfLe (show U' ⊓ V' ≤ U' from inf_le_left)) a b c h₁ h₂ ≫
        (unionPushoutIso U' V').hom = (unionPushoutIso U V).hom ≫ d := by
    apply pushout.hom_ext
    · simp only [Category.assoc, pushout.map, pushout.inl_desc_assoc]
      rw [(unionPushoutIso_legs U' V').1, ← Category.assoc,
        (unionPushoutIso_legs U V).1]
      exact h₃.symm
    · simp only [Category.assoc, pushout.map, pushout.inr_desc_assoc]
      rw [(unionPushoutIso_legs U' V').2.1, ← Category.assoc,
        (unionPushoutIso_legs U V).2.1]
      exact h₄.symm
  refine ⟨h, ?_⟩
  apply (cancel_mono (unionPushoutIso U' V').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h]
  simp [← Category.assoc]

end CategoryTheory.Subfunctor
