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

public import MathlibExt.CategoryTheory.Waldhausen.BinaryCoproductFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Coproduct cobase-change squares and cofibrations

In a category with a zero object and Waldhausen cofibration, weak-equivalence
and cofibration-pushout axioms, use the coproducts supplied by zero-source
pushouts. For any f:X → X′, the map f⊔1_Y lies in the pushout square
between the first injections X → X⊔Y and X′ → X′⊔Y.
Changing the second summand gives the analogous square.

If f and g are cofibrations, these squares and composition show that
f⊔g is a cofibration. Thus the coproduct functor sends pairs of
cofibrations to cofibrations.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

private theorem isPushoutOfBinaryCofans {X X' Y : C}
    {c : BinaryCofan X Y} {c' : BinaryCofan X' Y}
    (hc : IsColimit c) (hc' : IsColimit c') (f : X ⟶ X') (m : c.pt ⟶ c'.pt)
    (hL : c.inl ≫ m = f ≫ c'.inl) (hR : c.inr ≫ m = c'.inr) :
    IsPushout c.inl f m c'.inl := by
  let : HasBinaryCoproducts C := waldhausenHasBinaryCoproducts C
  let e : (X ⨿ Y) ≅ c.pt :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit (pair X Y)) hc
  let e' : (X' ⨿ Y) ≅ c'.pt :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit (pair X' Y)) hc'
  have heL : (coprod.inl : X ⟶ X ⨿ Y) ≫ e.hom = c.inl :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (pair X Y)) hc ⟨WalkingPair.left⟩
  have heR : (coprod.inr : Y ⟶ X ⨿ Y) ≫ e.hom = c.inr :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (pair X Y)) hc ⟨WalkingPair.right⟩
  have heL' : (coprod.inl : X' ⟶ X' ⨿ Y) ≫ e'.hom = c'.inl :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (pair X' Y)) hc' ⟨WalkingPair.left⟩
  have heR' : (coprod.inr : Y ⟶ X' ⨿ Y) ≫ e'.hom = c'.inr :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (pair X' Y)) hc' ⟨WalkingPair.right⟩
  have hm : (coprod.map f (𝟙 Y) : X ⨿ Y ⟶ X' ⨿ Y) ≫ e'.hom = e.hom ≫ m := by
    apply coprod.hom_ext
    · calc
        (coprod.inl : X ⟶ X ⨿ Y) ≫ (coprod.map f (𝟙 Y) ≫ e'.hom) =
            (f ≫ (coprod.inl : X' ⟶ X' ⨿ Y)) ≫ e'.hom := by
          rw [← Category.assoc, coprod.inl_map]
        _ = f ≫ ((coprod.inl : X' ⟶ X' ⨿ Y) ≫ e'.hom) := Category.assoc _ _ _
        _ = f ≫ c'.inl := by rw [heL']
        _ = c.inl ≫ m := hL.symm
        _ = ((coprod.inl : X ⟶ X ⨿ Y) ≫ e.hom) ≫ m := by rw [heL]
        _ = (coprod.inl : X ⟶ X ⨿ Y) ≫ (e.hom ≫ m) := Category.assoc _ _ _
    · calc
        (coprod.inr : Y ⟶ X ⨿ Y) ≫ (coprod.map f (𝟙 Y) ≫ e'.hom) =
            (𝟙 Y ≫ (coprod.inr : Y ⟶ X' ⨿ Y)) ≫ e'.hom := by
          rw [← Category.assoc, coprod.inr_map]
        _ = (coprod.inr : Y ⟶ X' ⨿ Y) ≫ e'.hom := by rw [Category.id_comp]
        _ = c'.inr := heR'
        _ = c.inr ≫ m := hR.symm
        _ = ((coprod.inr : Y ⟶ X ⨿ Y) ≫ e.hom) ≫ m := by rw [heR]
        _ = (coprod.inr : Y ⟶ X ⨿ Y) ≫ (e.hom ≫ m) := Category.assoc _ _ _
  apply (IsPushout.of_coprod_inl_with_id f Y).of_iso (Iso.refl X) e (Iso.refl X') e'
  · simpa only [Iso.refl_hom, Category.id_comp] using heL
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · exact hm
  · simpa only [Iso.refl_hom, Category.id_comp] using heL'

/-- Let C be a category with a zero object and Waldhausen cofibration,
weak-equivalence and cofibration-pushout axioms. Write X⊔Y for the chosen coproduct supplied by the
pushout of
0 → X and 0 → Y, with injections ι_X,ι_Y.

For any f:X → X′ and fixed Y, the square with maps ι_X:X → X⊔Y, f:X → X′, f⊔1_Y:X⊔Y → X′⊔Y and
ι_X′:X′ → X′⊔Y is a pushout. -/
theorem binaryCoproductMap_inl_isPushout {X X' : C} (f : X ⟶ X') (Y : C) :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone C (pair X Y)).cocone;
    let c' : BinaryCofan X' Y := (binaryCoproductColimitCocone C (pair X' Y)).cocone;
    IsPushout c.inl f (binaryCoproductMap C f (𝟙 Y)) c'.inl :=
  isPushoutOfBinaryCofans C
    (binaryCoproductColimitCocone C (pair X Y)).isColimit
    (binaryCoproductColimitCocone C (pair X' Y)).isColimit
    f (binaryCoproductMap C f (𝟙 Y)) (binaryCoproductMap_inl C f (𝟙 Y))
    ((binaryCoproductMap_inr C f (𝟙 Y)).trans (Category.id_comp _))

/-- Let C be a category with a zero object and Waldhausen cofibration,
weak-equivalence and cofibration-pushout axioms. Write X⊔Y for the chosen coproduct supplied by the
pushout of
0 → X and 0 → Y, with injections ι_X,ι_Y.

For fixed X and any g:Y → Y′, the square between the second injections Y → X⊔Y and Y′ → X⊔Y′, with
vertical maps g and 1_X⊔g, is a pushout. -/
theorem binaryCoproductMap_inr_isPushout (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone C (pair X Y)).cocone;
    let c' : BinaryCofan X Y' := (binaryCoproductColimitCocone C (pair X Y')).cocone;
    IsPushout c.inr g (binaryCoproductMap C (𝟙 X) g) c'.inr :=
  isPushoutOfBinaryCofans C
    (BinaryCofan.isColimitFlip (binaryCoproductColimitCocone C (pair X Y)).isColimit)
    (BinaryCofan.isColimitFlip (binaryCoproductColimitCocone C (pair X Y')).isColimit)
    g (binaryCoproductMap C (𝟙 X) g) (binaryCoproductMap_inr C (𝟙 X) g)
    ((binaryCoproductMap_inl C (𝟙 X) g).trans (Category.id_comp _))

/-- Let C be a category with a zero object and Waldhausen cofibration,
weak-equivalence and cofibration-pushout axioms. Write X⊔Y for the chosen coproduct supplied by the
pushout of
0 → X and 0 → Y, with injections ι_X,ι_Y.

For cofibrations f:X → X′ and g:Y → Y′, the induced map f⊔g:X⊔Y → X′⊔Y′ is a cofibration. -/
theorem binaryCoproductMap_isCofibration {X Y X' Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') (hf : IsCofibration f) (hg : IsCofibration g) :
    IsCofibration (binaryCoproductMap C f g) := by
  have h₁ : IsCofibration (binaryCoproductMap C f (𝟙 Y)) :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      (binaryCoproductMap_inl_isPushout C f Y) hf
  have h₂ : IsCofibration (binaryCoproductMap C (𝟙 X') g) :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      (binaryCoproductMap_inr_isPushout C X' g) hg
  have hcomp : binaryCoproductMap C f g =
      binaryCoproductMap C f (𝟙 Y) ≫ binaryCoproductMap C (𝟙 X') g := by
    simpa only [Category.comp_id, Category.id_comp] using
      binaryCoproductMap_comp C f (𝟙 Y) (𝟙 X') g
  rw [hcomp]
  exact (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).comp_mem _ _ h₁ h₂

/-- Let C be a category with a zero object and Waldhausen cofibration,
weak-equivalence and cofibration-pushout axioms. Write X⊔Y for the chosen coproduct supplied by the
pushout of
0 → X and 0 → Y, with injections ι_X,ι_Y.

For a pair morphism (f,g):(X,Y) → (X′,Y′) with both components cofibrations, its image under the
chosen coproduct functor C×C → C is a cofibration. -/
theorem waldhausenCoproductFunctor_map_isCofibration {p q : C × C} (f : p ⟶ q)
    (hf : IsCofibration f.1) (hg : IsCofibration f.2) :
    IsCofibration ((waldhausenCoproductFunctor C).map f) := by
  rw [waldhausenCoproductFunctor_map]
  refine (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).comp_mem _ _
    ((WaldhausenCategoryWithoutGluing.cofibrations (C := C)).of_isIso _) ?_
  exact (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).comp_mem _ _
    (binaryCoproductMap_isCofibration C f.1 f.2 hf hg)
    ((WaldhausenCategoryWithoutGluing.cofibrations (C := C)).of_isIso _)

end CategoryTheory.Waldhausen
