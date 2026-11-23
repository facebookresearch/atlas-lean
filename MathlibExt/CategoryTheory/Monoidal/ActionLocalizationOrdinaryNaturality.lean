/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.ActionLocalization

/-!
# Actual raw localized composition with ordinary morphisms

The original action associator and unitors normalize compositions with
ordinary inclusion arrows. Both equations are proved on the actual raw
stabilizer relation. They supply finite leaves for the actual zero-total
localized naturality square; no source arrow equality is assumed from its
middle coordinate or from a connected-component dictionary.
-/

noncomputable section

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory MonoidalLeftAction

universe uS vS uX vX

namespace CategoryTheory.MonoidalActionCategory

variable {S : Type uS} [Category.{vS} S] [MonoidalCategory S]
  {X : Type uX} [Category.{vX} X] [MonoidalLeftAction S X]

private theorem actualRawOrdinaryPostRelation
    {x y z : X} (T : S) (f : T ⊙ₗ x ⟶ y) (g : y ⟶ z) :
    ((⟨T, f⟩ : RawHom (⟨x⟩ : MonoidalActionCategory S X) ⟨y⟩).comp
      (RawHom.ofMap (S := S) g)).Rel
        (⟨T, f ≫ g⟩ : RawHom (⟨x⟩ : MonoidalActionCategory S X) ⟨z⟩) := by
  refine ⟨λ_ T, ?_⟩
  dsimp only [RawHom.comp, RawHom.ofMap]
  rw [MonoidalLeftAction.leftUnitor_actionHom, Category.assoc,
    MonoidalLeftAction.actionUnitIso_hom_naturality]
  simp only [MonoidalLeftAction.actionHomRight_comp, Category.assoc,
    MonoidalLeftAction.actionUnitIso_hom_naturality]

private theorem actualRawOrdinaryPreRelation
    {x y z : X} (T : S) (f : x ⟶ y) (g : T ⊙ₗ y ⟶ z) :
    ((RawHom.ofMap (S := S) f).comp
      (⟨T, g⟩ : RawHom (⟨y⟩ : MonoidalActionCategory S X) ⟨z⟩)).Rel
        (⟨T, T ⊴ₗ f ≫ g⟩ : RawHom (⟨x⟩ : MonoidalActionCategory S X) ⟨z⟩) := by
  refine ⟨ρ_ T, ?_⟩
  dsimp only [RawHom.comp, RawHom.ofMap]
  rw [MonoidalLeftAction.rightUnitor_actionHom]
  simp only [MonoidalLeftAction.actionHomRight_comp, Category.assoc]

private theorem actualCategoryRawPostComposition
    {x y z : X} (T : S) (f : T ⊙ₗ x ⟶ y) (g : y ⟶ z) :
    CategoryStruct.comp (obj := MonoidalActionCategory S X)
        (X := (⟨x⟩ : MonoidalActionCategory S X)) (Y := ⟨y⟩) (Z := ⟨z⟩)
        (Hom.mk (⟨T, f⟩ : RawHom (⟨x⟩ : MonoidalActionCategory S X) ⟨y⟩))
        ((inclusion S X).map g) =
      Hom.mk (⟨T, f ≫ g⟩ : RawHom (⟨x⟩ : MonoidalActionCategory S X) ⟨z⟩) := by
  rw [inclusion_map]
  exact (Hom.mk_comp
    (⟨T, f⟩ : RawHom (⟨x⟩ : MonoidalActionCategory S X) ⟨y⟩)
    (RawHom.ofMap (S := S) g)).trans
      (Quotient.sound (actualRawOrdinaryPostRelation T f g))

private theorem actualCategoryRawPreComposition
    {x y z : X} (T : S) (f : x ⟶ y) (g : T ⊙ₗ y ⟶ z) :
    CategoryStruct.comp (obj := MonoidalActionCategory S X)
        (X := (⟨x⟩ : MonoidalActionCategory S X)) (Y := ⟨y⟩) (Z := ⟨z⟩)
        ((inclusion S X).map f)
        (Hom.mk (⟨T, g⟩ : RawHom (⟨y⟩ : MonoidalActionCategory S X) ⟨z⟩)) =
      Hom.mk (⟨T, T ⊴ₗ f ≫ g⟩ : RawHom (⟨x⟩ : MonoidalActionCategory S X) ⟨z⟩) := by
  rw [inclusion_map]
  exact (Hom.mk_comp (RawHom.ofMap (S := S) f)
    (⟨T, g⟩ : RawHom (⟨y⟩ : MonoidalActionCategory S X) ⟨z⟩)).trans
      (Quotient.sound (actualRawOrdinaryPreRelation T f g))

/-- Actual postcomposition with an ordinary arrow retains the same raw stabilizer and hom. -/
public theorem hom_mk_postcompose_ordinary
    {x y z : X} (T : S) (f : T ⊙ₗ x ⟶ y) (g : y ⟶ z) :
    Hom.mk (⟨T, f⟩ : RawHom (⟨x⟩ : MonoidalActionCategory S X) ⟨y⟩) ≫
        (inclusion S X).map g =
      Hom.mk (⟨T, f ≫ g⟩ : RawHom (⟨x⟩ : MonoidalActionCategory S X) ⟨z⟩) :=
  actualCategoryRawPostComposition T f g

/-- Actual precomposition with an ordinary arrow uses its original action on the same stabilizer. -/
public theorem ordinary_precompose_hom_mk
    {x y z : X} (T : S) (f : x ⟶ y) (g : T ⊙ₗ y ⟶ z) :
    (inclusion S X).map f ≫
        Hom.mk (⟨T, g⟩ : RawHom (⟨y⟩ : MonoidalActionCategory S X) ⟨z⟩) =
      Hom.mk (⟨T, T ⊴ₗ f ≫ g⟩ : RawHom (⟨x⟩ : MonoidalActionCategory S X) ⟨z⟩) :=
  actualCategoryRawPreComposition T f g

private theorem actualLocalizedOrdinaryIntertwining
    {xL xR yL yR : X} (T : S) (f : T ⊙ₗ xL ⟶ yL) (g : T ⊙ₗ xR ⟶ yR)
    (a : xL ≅ xR) (b : yL ≅ yR) (h : f ≫ b.hom = T ⊴ₗ a.hom ≫ g) :
    Hom.mk (⟨T, f⟩ : RawHom (⟨xL⟩ : MonoidalActionCategory S X) ⟨yL⟩) ≫
        (inclusion S X).map b.hom =
      (inclusion S X).map a.hom ≫
        Hom.mk (⟨T, g⟩ : RawHom (⟨xR⟩ : MonoidalActionCategory S X) ⟨yR⟩) := by
  have hRaw := congrArg
    (fun k : T ⊙ₗ xL ⟶ yR =>
      Hom.mk (⟨T, k⟩ : RawHom (⟨xL⟩ : MonoidalActionCategory S X) ⟨yR⟩)) h
  exact (hom_mk_postcompose_ordinary T f b.hom).trans
    (hRaw.trans (ordinary_precompose_hom_mk T a.hom g).symm)

end CategoryTheory.MonoidalActionCategory

end
