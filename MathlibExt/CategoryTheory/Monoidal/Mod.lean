/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# General acted-category extensionality and `Mod.comap` coherence

Pinned `CategoryTheory.ModObj.ext` is restricted to self-action `X : C`,
while `ModObj` itself permits a general acted category `D`.
This file adds the smallest general version; it makes no upstream
subsumption claim.

It also provides generic identity and composition coherence for `Mod.comap`,
with underlying-cell computation lemmas.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.MonoidalLeftAction C D]
variable {M : C} [MonObj M]

/-- Extensionality for module objects over a general acted category `D`.
Pinned `ModObj.ext` covers only self-action `X : C`; this covers `X : D`.
No upstream subsumption is claimed. -/
@[to_additive (attr := ext)]
theorem ModObj.ext_general {X : D} (h₁ h₂ : ModObj M X)
    (H : h₁.smul = h₂.smul) : h₁ = h₂ := by
  cases h₁
  cases h₂
  subst H
  rfl

/-- Identity coherence for `Mod.comap`: restriction along `𝟙 A` is the identity. -/
@[to_additive]
def Mod.comapIdIso {A : C} [MonObj A] :
    (Mod.comap (D := D) (𝟙 A) : Mod D A ⥤ Mod D A) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M =>
      Iso.mk
        (Mod.Hom.mk' (𝟙 M.X) (by
          change (MonoidalCategory.MonoidalLeftAction.actionHomLeft
              (𝟙 A) M.X ≫ (M.mod).smul) ≫ 𝟙 M.X =
            MonoidalCategory.MonoidalLeftAction.actionHomRight
              A (𝟙 M.X) ≫ (M.mod).smul
          simp [MonoidalCategory.MonoidalLeftAction.id_actionHomLeft,
            MonoidalCategory.MonoidalLeftAction.actionHomRight_id]))
        (Mod.Hom.mk' (𝟙 M.X) (by
          change (M.mod).smul ≫ 𝟙 M.X =
            MonoidalCategory.MonoidalLeftAction.actionHomRight
              A (𝟙 M.X) ≫
              (MonoidalCategory.MonoidalLeftAction.actionHomLeft
                (𝟙 A) M.X ≫ (M.mod).smul)
          simp [MonoidalCategory.MonoidalLeftAction.id_actionHomLeft,
            MonoidalCategory.MonoidalLeftAction.actionHomRight_id]))
        (by
          apply Mod.hom_ext
          change (𝟙 M.X ≫ 𝟙 M.X) = 𝟙 M.X
          exact Category.comp_id _)
        (by
          apply Mod.hom_ext
          change (𝟙 M.X ≫ 𝟙 M.X) = 𝟙 M.X
          exact Category.comp_id _))
    (fun {X Y} f => by
      apply Mod.hom_ext
      change f.hom ≫ 𝟙 Y.X = 𝟙 X.X ≫ f.hom
      simp)

/-- Underlying-cell computation for the forward direction of `Mod.comapIdIso`. -/
@[to_additive (attr := simp)]
theorem Mod.comapIdIso_hom_app_hom {A : C} [MonObj A] (M : Mod D A) :
    (Mod.comapIdIso.hom.app M).hom = 𝟙 M.X :=
  rfl

/-- Underlying-cell computation for the inverse direction of `Mod.comapIdIso`. -/
@[to_additive (attr := simp) AddMod.comapIdIso_inv_app_hom]
theorem Mod.comapIdIso_inv_app_hom {A : C} [MonObj A] (M : Mod D A) :
    (Mod.comapIdIso.inv.app M).hom = 𝟙 M.X :=
  rfl

/-- Composition coherence for `Mod.comap`: restriction along `f ≫ g` factors
through the separate restrictions. -/
@[to_additive AddMod.comapCompIso]
def Mod.comapCompNatIso {A B E : C} [MonObj A] [MonObj B] [MonObj E]
    (f : A ⟶ B) (g : B ⟶ E) [IsMonHom f] [IsMonHom g] :
    (Mod.comap (D := D) (f ≫ g) : Mod D E ⥤ Mod D A) ≅
      Mod.comap g ⋙ Mod.comap f :=
  NatIso.ofComponents
    (fun M =>
      Iso.mk
        (Mod.Hom.mk' (𝟙 M.X) (by
          change (MonoidalCategory.MonoidalLeftAction.actionHomLeft
              (f ≫ g) M.X ≫ (M.mod).smul) ≫ 𝟙 M.X =
            MonoidalCategory.MonoidalLeftAction.actionHomRight
              A (𝟙 M.X) ≫
              (MonoidalCategory.MonoidalLeftAction.actionHomLeft
                f M.X ≫
                (MonoidalCategory.MonoidalLeftAction.actionHomLeft
                  g M.X ≫ (M.mod).smul))
          simp [MonoidalCategory.MonoidalLeftAction.actionHomRight_id,
            MonoidalCategory.MonoidalLeftAction.comp_actionHomLeft]))
        (Mod.Hom.mk' (𝟙 M.X) (by
          change (MonoidalCategory.MonoidalLeftAction.actionHomLeft
              f M.X ≫
              (MonoidalCategory.MonoidalLeftAction.actionHomLeft
                g M.X ≫ (M.mod).smul)) ≫ 𝟙 M.X =
            MonoidalCategory.MonoidalLeftAction.actionHomRight
              A (𝟙 M.X) ≫
              (MonoidalCategory.MonoidalLeftAction.actionHomLeft
                (f ≫ g) M.X ≫ (M.mod).smul)
          simp [MonoidalCategory.MonoidalLeftAction.actionHomRight_id,
            MonoidalCategory.MonoidalLeftAction.comp_actionHomLeft]))
        (by
          apply Mod.hom_ext
          change (𝟙 M.X ≫ 𝟙 M.X) = 𝟙 M.X
          exact Category.comp_id _)
        (by
          apply Mod.hom_ext
          change (𝟙 M.X ≫ 𝟙 M.X) = 𝟙 M.X
          exact Category.comp_id _))
    (fun {X Y} h => by
      apply Mod.hom_ext
      change h.hom ≫ 𝟙 Y.X = 𝟙 X.X ≫ h.hom
      simp)

/-- Underlying-cell computation for the forward direction of `Mod.comapCompNatIso`. -/
@[to_additive (attr := simp)]
theorem Mod.comapCompIso_hom_app_hom {A B E : C} [MonObj A] [MonObj B]
    [MonObj E] (f : A ⟶ B) (g : B ⟶ E) [IsMonHom f] [IsMonHom g]
    (M : Mod D E) :
    ((Mod.comapCompNatIso f g).hom.app M).hom = 𝟙 M.X :=
  rfl

/-- Underlying-cell computation for the inverse direction of `Mod.comapCompNatIso`. -/
@[to_additive (attr := simp) AddMod.comapCompIso_inv_app_hom]
theorem Mod.comapCompIso_inv_app_hom {A B E : C} [MonObj A] [MonObj B]
    [MonObj E] (f : A ⟶ B) (g : B ⟶ E) [IsMonHom f] [IsMonHom g]
    (M : Mod D E) :
    ((Mod.comapCompNatIso f g).inv.app M).hom = 𝟙 M.X :=
  rfl

end CategoryTheory
