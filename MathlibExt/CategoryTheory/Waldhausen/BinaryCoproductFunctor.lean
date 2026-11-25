/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.BinaryCoproduct
public import Mathlib.CategoryTheory.Products.Basic

/-!
# The functor of the derived Waldhausen coproduct

Objects are the actual coproduct cocones already derived from zero
pushouts. Morphisms are their colimit descendants. The two injection
equations prove the functor laws. Whole map equations retain the proved
object transports, so callers need no unfolding of the functor value.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The actual map between the derived coproduct cocones, determined by
the two original component maps. -/
noncomputable def binaryCoproductMap {X Y X' Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone C (pair X Y)).cocone;
    let c' : BinaryCofan X' Y' := (binaryCoproductColimitCocone C (pair X' Y')).cocone;
    c.pt ⟶ c'.pt :=
  BinaryCofan.IsColimit.desc (binaryCoproductColimitCocone C (pair X Y)).isColimit
    (f ≫ (binaryCoproductColimitCocone C (pair X' Y')).cocone.ι.app ⟨WalkingPair.left⟩)
    (g ≫ (binaryCoproductColimitCocone C (pair X' Y')).cocone.ι.app ⟨WalkingPair.right⟩)

private theorem binaryCoproductMap_inl_aux {X Y X' Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone C (pair X Y)).cocone;
    let c' : BinaryCofan X' Y' := (binaryCoproductColimitCocone C (pair X' Y')).cocone;
    c.inl ≫ binaryCoproductMap C f g = f ≫ c'.inl := by
  unfold binaryCoproductMap
  exact BinaryCofan.IsColimit.inl_desc
    (binaryCoproductColimitCocone C (pair X Y)).isColimit _ _

/-- The map sends the first injection through the original first map. -/
theorem binaryCoproductMap_inl {X Y X' Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone C (pair X Y)).cocone;
    let c' : BinaryCofan X' Y' := (binaryCoproductColimitCocone C (pair X' Y')).cocone;
    c.inl ≫ binaryCoproductMap C f g = f ≫ c'.inl :=
  binaryCoproductMap_inl_aux C f g

private theorem binaryCoproductMap_inr_aux {X Y X' Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone C (pair X Y)).cocone;
    let c' : BinaryCofan X' Y' := (binaryCoproductColimitCocone C (pair X' Y')).cocone;
    c.inr ≫ binaryCoproductMap C f g = g ≫ c'.inr := by
  unfold binaryCoproductMap
  exact BinaryCofan.IsColimit.inr_desc
    (binaryCoproductColimitCocone C (pair X Y)).isColimit _ _

/-- The map sends the second injection through the original second map. -/
theorem binaryCoproductMap_inr {X Y X' Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone C (pair X Y)).cocone;
    let c' : BinaryCofan X' Y' := (binaryCoproductColimitCocone C (pair X' Y')).cocone;
    c.inr ≫ binaryCoproductMap C f g = g ≫ c'.inr :=
  binaryCoproductMap_inr_aux C f g

/-- Identity component maps give the identity of the actual coproduct. -/
theorem binaryCoproductMap_id (X Y : C) :
    binaryCoproductMap C (𝟙 X) (𝟙 Y) =
      𝟙 (binaryCoproductColimitCocone C (pair X Y)).cocone.pt := by
  apply BinaryCofan.IsColimit.hom_ext
    (binaryCoproductColimitCocone C (pair X Y)).isColimit
  · simpa only [Category.id_comp, Category.comp_id] using
      binaryCoproductMap_inl C (𝟙 X) (𝟙 Y)
  · simpa only [Category.id_comp, Category.comp_id] using
      binaryCoproductMap_inr C (𝟙 X) (𝟙 Y)

/-- The actual coproduct maps compose in both original components. -/
theorem binaryCoproductMap_comp {X₀ Y₀ X₁ Y₁ X₂ Y₂ : C}
    (f₀ : X₀ ⟶ X₁) (g₀ : Y₀ ⟶ Y₁) (f₁ : X₁ ⟶ X₂) (g₁ : Y₁ ⟶ Y₂) :
    binaryCoproductMap C (f₀ ≫ f₁) (g₀ ≫ g₁) =
      binaryCoproductMap C f₀ g₀ ≫ binaryCoproductMap C f₁ g₁ := by
  let c₀ : BinaryCofan X₀ Y₀ := (binaryCoproductColimitCocone C (pair X₀ Y₀)).cocone
  let c₁ : BinaryCofan X₁ Y₁ := (binaryCoproductColimitCocone C (pair X₁ Y₁)).cocone
  let c₂ : BinaryCofan X₂ Y₂ := (binaryCoproductColimitCocone C (pair X₂ Y₂)).cocone
  apply BinaryCofan.IsColimit.hom_ext (binaryCoproductColimitCocone C (pair X₀ Y₀)).isColimit
  · calc
      c₀.inl ≫ binaryCoproductMap C (f₀ ≫ f₁) (g₀ ≫ g₁) =
          (f₀ ≫ f₁) ≫ c₂.inl := binaryCoproductMap_inl C _ _
      _ = f₀ ≫ (f₁ ≫ c₂.inl) := Category.assoc _ _ _
      _ = f₀ ≫ (c₁.inl ≫ binaryCoproductMap C f₁ g₁) := by rw [binaryCoproductMap_inl]
      _ = (f₀ ≫ c₁.inl) ≫ binaryCoproductMap C f₁ g₁ := (Category.assoc _ _ _).symm
      _ = (c₀.inl ≫ binaryCoproductMap C f₀ g₀) ≫ binaryCoproductMap C f₁ g₁ := by
        rw [binaryCoproductMap_inl]
      _ = c₀.inl ≫ (binaryCoproductMap C f₀ g₀ ≫ binaryCoproductMap C f₁ g₁) :=
        Category.assoc _ _ _
  · calc
      c₀.inr ≫ binaryCoproductMap C (f₀ ≫ f₁) (g₀ ≫ g₁) =
          (g₀ ≫ g₁) ≫ c₂.inr := binaryCoproductMap_inr C _ _
      _ = g₀ ≫ (g₁ ≫ c₂.inr) := Category.assoc _ _ _
      _ = g₀ ≫ (c₁.inr ≫ binaryCoproductMap C f₁ g₁) := by rw [binaryCoproductMap_inr]
      _ = (g₀ ≫ c₁.inr) ≫ binaryCoproductMap C f₁ g₁ := (Category.assoc _ _ _).symm
      _ = (c₀.inr ≫ binaryCoproductMap C f₀ g₀) ≫ binaryCoproductMap C f₁ g₁ := by
        rw [binaryCoproductMap_inr]
      _ = c₀.inr ≫ (binaryCoproductMap C f₀ g₀ ≫ binaryCoproductMap C f₁ g₁) :=
        Category.assoc _ _ _

/-- The original zero-pushout coproduct cocones form a functor on pairs. -/
noncomputable def waldhausenCoproductFunctor : C × C ⥤ C where
  obj p := (binaryCoproductColimitCocone C (pair p.1 p.2)).cocone.pt
  map f := binaryCoproductMap C f.1 f.2
  map_id p := binaryCoproductMap_id C p.1 p.2
  map_comp f g := binaryCoproductMap_comp C f.1 f.2 g.1 g.2

private theorem waldhausenCoproductFunctor_obj_aux (p : C × C) :
    (waldhausenCoproductFunctor C).obj p =
      (binaryCoproductColimitCocone C (pair p.1 p.2)).cocone.pt := by
  rfl

/-- The functor object is the apex of the existing derived coproduct. -/
theorem waldhausenCoproductFunctor_obj (p : C × C) :
    (waldhausenCoproductFunctor C).obj p =
      (binaryCoproductColimitCocone C (pair p.1 p.2)).cocone.pt :=
  waldhausenCoproductFunctor_obj_aux C p

private theorem waldhausenCoproductFunctor_map_heq_aux {p q : C × C} (f : p ⟶ q) :
    HEq ((waldhausenCoproductFunctor C).map f) (binaryCoproductMap C f.1 f.2) := by
  rfl

/-- The whole functor map is the actual coproduct descendant through the
proved source and target object transports. -/
theorem waldhausenCoproductFunctor_map {p q : C × C} (f : p ⟶ q) :
    (waldhausenCoproductFunctor C).map f =
      eqToHom (waldhausenCoproductFunctor_obj C p) ≫ binaryCoproductMap C f.1 f.2 ≫
        eqToHom (waldhausenCoproductFunctor_obj C q).symm :=
  (conj_eqToHom_iff_heq _ _
    (waldhausenCoproductFunctor_obj C p) (waldhausenCoproductFunctor_obj C q)).2
      (waldhausenCoproductFunctor_map_heq_aux C f)

end CategoryTheory.Waldhausen
