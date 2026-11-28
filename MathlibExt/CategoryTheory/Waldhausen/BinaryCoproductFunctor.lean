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
# The chosen coproduct functor in a Waldhausen category

Let C have a zero object and Waldhausen cofibration, weak-equivalence
and cofibration-pushout axioms. Its chosen zero-source pushouts are binary
coproducts. Maps f:X → X′ and g:Y → Y′ induce the unique coproduct map
f⊔g characterized by its two injection equations.

These maps respect identities and composition, giving a functor C×C → C
whose value on (X,Y) is the chosen coproduct apex. Its map on a pair of
morphisms is the coproduct map under the canonical apex identifications.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Let C be a category with a zero object and Waldhausen cofibration,
weak-equivalence and cofibration-pushout axioms. Write X⊔Y for the chosen coproduct supplied by the
pushout of
0 → X and 0 → Y, with injections ι_X,ι_Y.

For f:X → X′ and g:Y → Y′, the induced map f⊔g between the chosen coproduct apices is the unique map
with (f⊔g)∘ι_X=ι_X′∘f and (f⊔g)∘ι_Y=ι_Y′∘g. -/
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

/-- Let C be a category with a zero object and Waldhausen cofibration,
weak-equivalence and cofibration-pushout axioms. Write X⊔Y for the chosen coproduct supplied by the
pushout of
0 → X and 0 → Y, with injections ι_X,ι_Y.

For f:X → X′ and g:Y → Y′, the first injection equation is (f⊔g)∘ι_X=ι_X′∘f. -/
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

/-- Let C be a category with a zero object and Waldhausen cofibration,
weak-equivalence and cofibration-pushout axioms. Write X⊔Y for the chosen coproduct supplied by the
pushout of
0 → X and 0 → Y, with injections ι_X,ι_Y.

For f:X → X′ and g:Y → Y′, the second injection equation is (f⊔g)∘ι_Y=ι_Y′∘g. -/
theorem binaryCoproductMap_inr {X Y X' Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone C (pair X Y)).cocone;
    let c' : BinaryCofan X' Y' := (binaryCoproductColimitCocone C (pair X' Y')).cocone;
    c.inr ≫ binaryCoproductMap C f g = g ≫ c'.inr :=
  binaryCoproductMap_inr_aux C f g

/-- Let C be a category with a zero object and Waldhausen cofibration,
weak-equivalence and cofibration-pushout axioms. Write X⊔Y for the chosen coproduct supplied by the
pushout of
0 → X and 0 → Y, with injections ι_X,ι_Y.

The map induced by 1_X and 1_Y is the identity of X⊔Y. -/
theorem binaryCoproductMap_id (X Y : C) :
    binaryCoproductMap C (𝟙 X) (𝟙 Y) =
      𝟙 (binaryCoproductColimitCocone C (pair X Y)).cocone.pt := by
  apply BinaryCofan.IsColimit.hom_ext
    (binaryCoproductColimitCocone C (pair X Y)).isColimit
  · simpa only [Category.id_comp, Category.comp_id] using
      binaryCoproductMap_inl C (𝟙 X) (𝟙 Y)
  · simpa only [Category.id_comp, Category.comp_id] using
      binaryCoproductMap_inr C (𝟙 X) (𝟙 Y)

/-- Let C be a category with a zero object and Waldhausen cofibration,
weak-equivalence and cofibration-pushout axioms. Write X⊔Y for the chosen coproduct supplied by the
pushout of
0 → X and 0 → Y, with injections ι_X,ι_Y.

For composable f₀,f₁ and g₀,g₁, the chosen maps satisfy (f₁∘f₀)⊔(g₁∘g₀)=(f₁⊔g₁)∘(f₀⊔g₀). -/
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

/-- Let C be a category with a zero object and Waldhausen cofibration,
weak-equivalence and cofibration-pushout axioms. Write X⊔Y for the chosen coproduct supplied by the
pushout of
0 → X and 0 → Y, with injections ι_X,ι_Y.

The functor C×C → C sending (X,Y) to the chosen coproduct apex and (f,g) to its induced coproduct
map. -/
noncomputable def waldhausenCoproductFunctor : C × C ⥤ C where
  obj p := (binaryCoproductColimitCocone C (pair p.1 p.2)).cocone.pt
  map f := binaryCoproductMap C f.1 f.2
  map_id p := binaryCoproductMap_id C p.1 p.2
  map_comp f g := binaryCoproductMap_comp C f.1 f.2 g.1 g.2

private theorem waldhausenCoproductFunctor_obj_aux (p : C × C) :
    (waldhausenCoproductFunctor C).obj p =
      (binaryCoproductColimitCocone C (pair p.1 p.2)).cocone.pt := by
  rfl

/-- Let C be a category with a zero object and Waldhausen cofibration,
weak-equivalence and cofibration-pushout axioms. Write X⊔Y for the chosen coproduct supplied by the
pushout of
0 → X and 0 → Y, with injections ι_X,ι_Y.

At a pair (X,Y), the coproduct functor has value the apex of the selected zero-source coproduct
cocone. -/
theorem waldhausenCoproductFunctor_obj (p : C × C) :
    (waldhausenCoproductFunctor C).obj p =
      (binaryCoproductColimitCocone C (pair p.1 p.2)).cocone.pt :=
  waldhausenCoproductFunctor_obj_aux C p

private theorem waldhausenCoproductFunctor_map_heq_aux {p q : C × C} (f : p ⟶ q) :
    HEq ((waldhausenCoproductFunctor C).map f) (binaryCoproductMap C f.1 f.2) := by
  rfl

/-- Let C be a category with a zero object and Waldhausen cofibration,
weak-equivalence and cofibration-pushout axioms. Write X⊔Y for the chosen coproduct supplied by the
pushout of
0 → X and 0 → Y, with injections ι_X,ι_Y.

Under the canonical identifications of the functor values with the selected coproduct apices, its
map on (f,g) is the unique coproduct map f⊔g. -/
theorem waldhausenCoproductFunctor_map {p q : C × C} (f : p ⟶ q) :
    (waldhausenCoproductFunctor C).map f =
      eqToHom (waldhausenCoproductFunctor_obj C p) ≫ binaryCoproductMap C f.1 f.2 ≫
        eqToHom (waldhausenCoproductFunctor_obj C q).symm :=
  (conj_eqToHom_iff_heq _ _
    (waldhausenCoproductFunctor_obj C p) (waldhausenCoproductFunctor_obj C q)).2
      (waldhausenCoproductFunctor_map_heq_aux C f)

end CategoryTheory.Waldhausen
