/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Subfunctor.UnionPushout

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace MathlibExtTest.SubfunctorUnionPushout

variable {J : Type u} [Category.{v} J] {F F' W : J ⥤ Type w}

example (U V : Subfunctor F) :
    IsPushout (Subfunctor.homOfLe (show U ⊓ V ≤ V from inf_le_right))
      (Subfunctor.homOfLe (show U ⊓ V ≤ U from inf_le_left))
      (Subfunctor.homOfLe (show V ≤ U ⊔ V from le_sup_right))
      (Subfunctor.homOfLe (show U ≤ U ⊔ V from le_sup_left)) :=
  Subfunctor.isPushout_inf_sup U V

example (U V : Subfunctor F) (f : V.toFunctor ⟶ W) (g : U.toFunctor ⟶ W)
    (h : Subfunctor.homOfLe (show U ⊓ V ≤ V from inf_le_right) ≫ f =
      Subfunctor.homOfLe (show U ⊓ V ≤ U from inf_le_left) ≫ g) :
    Subfunctor.homOfLe (show V ≤ U ⊔ V from le_sup_right) ≫
      (Subfunctor.isPushout_inf_sup U V).desc f g h = f :=
  (Subfunctor.isPushout_inf_sup U V).inl_desc f g h

example (U V : Subfunctor F) (f : V.toFunctor ⟶ W) (g : U.toFunctor ⟶ W)
    (h : Subfunctor.homOfLe (show U ⊓ V ≤ V from inf_le_right) ≫ f =
      Subfunctor.homOfLe (show U ⊓ V ≤ U from inf_le_left) ≫ g) :
    Subfunctor.homOfLe (show U ≤ U ⊔ V from le_sup_left) ≫
      (Subfunctor.isPushout_inf_sup U V).desc f g h = g :=
  (Subfunctor.isPushout_inf_sup U V).inr_desc f g h

example (U V : Subfunctor F) (f : V.toFunctor ⟶ W) (g : U.toFunctor ⟶ W)
    (h : Subfunctor.homOfLe (show U ⊓ V ≤ V from inf_le_right) ≫ f =
      Subfunctor.homOfLe (show U ⊓ V ≤ U from inf_le_left) ≫ g)
    (d : (U ⊔ V).toFunctor ⟶ W)
    (hV : Subfunctor.homOfLe (show V ≤ U ⊔ V from le_sup_right) ≫ d = f)
    (hU : Subfunctor.homOfLe (show U ≤ U ⊔ V from le_sup_left) ≫ d = g) :
    d = (Subfunctor.isPushout_inf_sup U V).desc f g h :=
  (Subfunctor.isPushout_inf_sup U V).hom_ext
    (hV.trans ((Subfunctor.isPushout_inf_sup U V).inl_desc f g h).symm)
    (hU.trans ((Subfunctor.isPushout_inf_sup U V).inr_desc f g h).symm)

example (U V : Subfunctor F) :
    Subfunctor.homOfLe (show V ≤ U ⊔ V from le_sup_right) ≫
      (Subfunctor.unionPushoutIso U V).inv =
      pushout.inl (Subfunctor.homOfLe (show U ⊓ V ≤ V from inf_le_right))
        (Subfunctor.homOfLe (show U ⊓ V ≤ U from inf_le_left)) :=
  (Subfunctor.unionPushoutIso_legs U V).2.2.1

example (U V : Subfunctor F) :
    Subfunctor.homOfLe (show U ≤ U ⊔ V from le_sup_left) ≫
      (Subfunctor.unionPushoutIso U V).inv =
      pushout.inr (Subfunctor.homOfLe (show U ⊓ V ≤ V from inf_le_right))
        (Subfunctor.homOfLe (show U ⊓ V ≤ U from inf_le_left)) :=
  (Subfunctor.unionPushoutIso_legs U V).2.2.2

example (U V : Subfunctor F) (U' V' : Subfunctor F')
    (a : V.toFunctor ⟶ V'.toFunctor) (b : U.toFunctor ⟶ U'.toFunctor)
    (c : (U ⊓ V).toFunctor ⟶ (U' ⊓ V').toFunctor)
    (d : (U ⊔ V).toFunctor ⟶ (U' ⊔ V').toFunctor)
    (h₁ : Subfunctor.homOfLe (show U ⊓ V ≤ V from inf_le_right) ≫ a =
      c ≫ Subfunctor.homOfLe (show U' ⊓ V' ≤ V' from inf_le_right))
    (h₂ : Subfunctor.homOfLe (show U ⊓ V ≤ U from inf_le_left) ≫ b =
      c ≫ Subfunctor.homOfLe (show U' ⊓ V' ≤ U' from inf_le_left))
    (h₃ : Subfunctor.homOfLe (show V ≤ U ⊔ V from le_sup_right) ≫ d =
      a ≫ Subfunctor.homOfLe (show V' ≤ U' ⊔ V' from le_sup_right))
    (h₄ : Subfunctor.homOfLe (show U ≤ U ⊔ V from le_sup_left) ≫ d =
      b ≫ Subfunctor.homOfLe (show U' ≤ U' ⊔ V' from le_sup_left)) :
    let m := pushout.map
      (Subfunctor.homOfLe (show U ⊓ V ≤ V from inf_le_right))
      (Subfunctor.homOfLe (show U ⊓ V ≤ U from inf_le_left))
      (Subfunctor.homOfLe (show U' ⊓ V' ≤ V' from inf_le_right))
      (Subfunctor.homOfLe (show U' ⊓ V' ≤ U' from inf_le_left)) a b c h₁ h₂
    (m ≫ (Subfunctor.unionPushoutIso U' V').hom =
      (Subfunctor.unionPushoutIso U V).hom ≫ d) ∧
      (d ≫ (Subfunctor.unionPushoutIso U' V').inv =
        (Subfunctor.unionPushoutIso U V).inv ≫ m) :=
  Subfunctor.unionPushoutIso_naturality U V U' V' a b c d h₁ h₂ h₃ h₄

end MathlibExtTest.SubfunctorUnionPushout
