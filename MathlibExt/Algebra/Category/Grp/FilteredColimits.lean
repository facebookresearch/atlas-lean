/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Filtered colimits in `GrpCat`

Filtered colimits of groups and the induced maps `colimitMap` / `colimitFunctor`
constructed via the auxiliary cocone `mapCocone`.
-/

@[expose] public section

universe v u

noncomputable section

open CategoryTheory Limits

namespace GrpCat.FilteredColimits

variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable {D₁ D₂ D₃ : J ⥤ GrpCat.{max v u}}

/-- Cocone inducing the map `colimitMap` on filtered colimits. -/
noncomputable def mapCocone {D₁ D₂ : J ⥤ GrpCat.{max v u}} (α : D₁ ⟶ D₂) :
    Cocone D₁ where
  pt := (colimitCocone (F := D₂)).pt
  ι :=
    { app := fun j => α.app j ≫ (colimitCocone (F := D₂)).ι.app j
      naturality := fun j₁ j₂ f => by
        have hα : D₁.map f ≫ α.app j₂ = α.app j₁ ≫ D₂.map f := α.naturality f
        have hD₂ : D₂.map f ≫ (colimitCocone (F := D₂)).ι.app j₂ =
            (colimitCocone (F := D₂)).ι.app j₁ := by
          have h := (colimitCocone (F := D₂)).ι.naturality f
          simp only [Functor.const_obj_map] at h
          exact h
        calc
          D₁.map f ≫ α.app j₂ ≫ (colimitCocone (F := D₂)).ι.app j₂
              = α.app j₁ ≫ (colimitCocone (F := D₂)).ι.app j₁ := by
                calc
                  D₁.map f ≫ α.app j₂ ≫ (colimitCocone (F := D₂)).ι.app j₂
                      = α.app j₁ ≫ D₂.map f ≫ (colimitCocone (F := D₂)).ι.app j₂ := by
                        rw [← Category.assoc, hα, Category.assoc]
                  _ = α.app j₁ ≫ (colimitCocone (F := D₂)).ι.app j₁ := by rw [hD₂]
          _ = (α.app j₁ ≫ (colimitCocone (F := D₂)).ι.app j₁) ≫
                𝟙 ((colimitCocone (F := D₂)).pt) :=
            (Category.comp_id _).symm
          _ = (α.app j₁ ≫ (colimitCocone (F := D₂)).ι.app j₁) ≫
                ((Functor.const J).obj (colimitCocone (F := D₂)).pt).map f := rfl }

/-- Induced map on filtered colimits for a morphism of diagrams. -/
noncomputable def colimitMap {D₁ D₂ : J ⥤ GrpCat.{max v u}} (α : D₁ ⟶ D₂) :
    (colimitCocone D₁).pt ⟶ (colimitCocone D₂).pt :=
  (colimitCoconeIsColimit (F := D₁)).desc (mapCocone α)

@[simp]
theorem colimitMap_ι {D₁ D₂ : J ⥤ GrpCat.{max v u}} (α : D₁ ⟶ D₂) (j : J) :
    (colimitCocone D₁).ι.app j ≫ colimitMap α =
      α.app j ≫ (colimitCocone D₂).ι.app j := by
  have hfac := (colimitCoconeIsColimit (F := D₁)).fac (mapCocone α) j
  exact hfac

theorem colimitMap_ι_apply {D₁ D₂ : J ⥤ GrpCat.{max v u}} (α : D₁ ⟶ D₂) (j : J)
    (x : D₁.obj j) :
    (colimitMap α) ((colimitCocone D₁).ι.app j x) =
      (colimitCocone D₂).ι.app j (α.app j x) :=
  ConcreteCategory.congr_hom (colimitMap_ι α j) x

theorem colimitMap_mk {D₁ D₂ : J ⥤ GrpCat.{max v u}} (α : D₁ ⟶ D₂) (j : J)
    (x : D₁.obj j) :
    (colimitMap α) (G.mk (F := D₁) ⟨j, x⟩) =
      G.mk (F := D₂) ⟨j, (α.app j) x⟩ := by
  have h₁ : (colimitCocone (F := D₁)).ι.app j x = G.mk (F := D₁) ⟨j, x⟩ := rfl
  have h₂ : (colimitCocone (F := D₂)).ι.app j ((α.app j) x) =
      G.mk (F := D₂) ⟨j, (α.app j) x⟩ := rfl
  have h3 : colimitMap α (G.mk (F := D₁) ⟨j, x⟩) =
      (colimitCocone D₂).ι.app j (α.app j x) := by
    have h : colimitMap α ((colimitCocone D₁).ι.app j x) =
        (colimitCocone D₂).ι.app j (α.app j x) := colimitMap_ι_apply α j x
    have : G.mk (F := D₁) ⟨j, x⟩ = (colimitCocone D₁).ι.app j x := h₁.symm
    calc
      colimitMap α (G.mk (F := D₁) ⟨j, x⟩)
          = colimitMap α ((colimitCocone D₁).ι.app j x) := by rw [this]
      _ = (colimitCocone D₂).ι.app j (α.app j x) := h
  exact h3.trans h₂.symm

theorem colimitMap_id (D : J ⥤ GrpCat.{max v u}) :
    colimitMap (𝟙 D) = 𝟙 ((colimitCocone D).pt) := by
  apply (colimitCoconeIsColimit D).hom_ext
  intro j
  have h : (colimitCocone D).ι.app j ≫ colimitMap (𝟙 D) =
      (colimitCocone D).ι.app j := by
    simp [colimitMap_ι]
  calc
    (colimitCocone D).ι.app j ≫ colimitMap (𝟙 D)
        = (colimitCocone D).ι.app j := h
    _ = (colimitCocone D).ι.app j ≫ 𝟙 ((colimitCocone D).pt) := by simp

theorem colimitMap_comp {D₁ D₂ D₃ : J ⥤ GrpCat.{max v u}} (α : D₁ ⟶ D₂) (β : D₂ ⟶ D₃) :
    colimitMap (α ≫ β) = colimitMap α ≫ colimitMap β := by
  apply (colimitCoconeIsColimit D₁).hom_ext
  intro j
  calc
    (colimitCocone D₁).ι.app j ≫ colimitMap (α ≫ β)
        = (α ≫ β).app j ≫ (colimitCocone D₃).ι.app j := colimitMap_ι _ _
    _ = (α.app j ≫ β.app j) ≫ (colimitCocone D₃).ι.app j := rfl
    _ = α.app j ≫ β.app j ≫ (colimitCocone D₃).ι.app j := by rw [Category.assoc]
    _ = α.app j ≫ ((colimitCocone D₂).ι.app j ≫ colimitMap β) := by
          rw [← colimitMap_ι (α := β)]
    _ = (α.app j ≫ (colimitCocone D₂).ι.app j) ≫ colimitMap β := by rw [← Category.assoc]
    _ = ((colimitCocone D₁).ι.app j ≫ colimitMap α) ≫ colimitMap β := by
          rw [← colimitMap_ι (α := α)]
    _ = (colimitCocone D₁).ι.app j ≫ colimitMap α ≫ colimitMap β := by rw [Category.assoc]

/-- Filtered-colimit functor on `GrpCat`. -/
noncomputable def colimitFunctor : (J ⥤ GrpCat.{max v u}) ⥤ GrpCat.{max v u} where
  obj F := colimit F
  map α := colimitMap α
  map_id _ := colimitMap_id _
  map_comp α β := colimitMap_comp α β

@[simp]
theorem colimitFunctor_obj (F : J ⥤ GrpCat.{max v u}) :
    (colimitFunctor (J := J)).obj F = colimit F :=
  rfl

@[simp]
theorem colimitFunctor_map {D₁ D₂ : J ⥤ GrpCat.{max v u}} (α : D₁ ⟶ D₂) :
    (colimitFunctor (J := J)).map α = colimitMap α :=
  rfl

end GrpCat.FilteredColimits
