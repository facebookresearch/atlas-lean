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
public import MathlibExt.CategoryTheory.Products.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Pushout preservation of the actual derived coproduct

The two source pushouts form a pointwise pushout of walking-pair
diagrams. The existing colimit adjunction carries this square to a
pushout of canonical coproducts. Colimit-apex isomorphisms transport it
to the fixed derived coproduct cocones, and the earned functor object
isomorphisms give the actual whole functor square.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Two actual component pushouts give a pushout of the fixed derived
coproduct apices and their original maps. -/
theorem binaryCoproductMap_isPushout {X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃ : C}
    (t₀ : X₀ ⟶ X₁) (t₁ : Y₀ ⟶ Y₁) (l₀ : X₀ ⟶ X₂) (l₁ : Y₀ ⟶ Y₂)
    (r₀ : X₁ ⟶ X₃) (r₁ : Y₁ ⟶ Y₃) (b₀ : X₂ ⟶ X₃) (b₁ : Y₂ ⟶ Y₃)
    (h₀ : IsPushout t₀ l₀ r₀ b₀) (h₁ : IsPushout t₁ l₁ r₁ b₁) :
    IsPushout (binaryCoproductMap C t₀ t₁) (binaryCoproductMap C l₀ l₁)
      (binaryCoproductMap C r₀ r₁) (binaryCoproductMap C b₀ b₁) := by
  let : HasBinaryCoproducts C := waldhausenHasBinaryCoproducts C
  have hdiag : IsPushout
      (mapPair t₀ t₁ : pair X₀ Y₀ ⟶ pair X₁ Y₁)
      (mapPair l₀ l₁ : pair X₀ Y₀ ⟶ pair X₂ Y₂)
      (mapPair r₀ r₁ : pair X₁ Y₁ ⟶ pair X₃ Y₃)
      (mapPair b₀ b₁ : pair X₂ Y₂ ⟶ pair X₃ Y₃) := by
    apply IsPushout.of_forall_isPushout_app
    intro j
    rcases j with ⟨j⟩
    cases j
    · simpa only [mapPair_left] using h₀
    · simpa only [mapPair_right] using h₁
  have hstd := hdiag.map (colim (J := Discrete WalkingPair) (C := C))
  change IsPushout (coprod.map t₀ t₁) (coprod.map l₀ l₁)
    (coprod.map r₀ r₁) (coprod.map b₀ b₁) at hstd
  let e (X Y : C) : (X ⨿ Y) ≅ (binaryCoproductColimitCocone C (pair X Y)).cocone.pt :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit (pair X Y))
      (binaryCoproductColimitCocone C (pair X Y)).isColimit
  have heL (X Y : C) : (coprod.inl : X ⟶ X ⨿ Y) ≫ (e X Y).hom =
      (binaryCoproductColimitCocone C (pair X Y)).cocone.ι.app ⟨WalkingPair.left⟩ :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (pair X Y))
      (binaryCoproductColimitCocone C (pair X Y)).isColimit ⟨WalkingPair.left⟩
  have heR (X Y : C) : (coprod.inr : Y ⟶ X ⨿ Y) ≫ (e X Y).hom =
      (binaryCoproductColimitCocone C (pair X Y)).cocone.ι.app ⟨WalkingPair.right⟩ :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (pair X Y))
      (binaryCoproductColimitCocone C (pair X Y)).isColimit ⟨WalkingPair.right⟩
  have hm {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
      (coprod.map f g : X ⨿ Y ⟶ X' ⨿ Y') ≫ (e X' Y').hom =
        (e X Y).hom ≫ binaryCoproductMap C f g := by
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone C (pair X Y)).cocone
    let c' : BinaryCofan X' Y' := (binaryCoproductColimitCocone C (pair X' Y')).cocone
    apply coprod.hom_ext
    · calc
        (coprod.inl : X ⟶ X ⨿ Y) ≫ (coprod.map f g ≫ (e X' Y').hom) =
            f ≫ ((coprod.inl : X' ⟶ X' ⨿ Y') ≫ (e X' Y').hom) := by
          rw [← Category.assoc, coprod.inl_map, Category.assoc]
        _ = f ≫ c'.inl := by rw [heL]
        _ = c.inl ≫ binaryCoproductMap C f g := (binaryCoproductMap_inl C f g).symm
        _ = (coprod.inl : X ⟶ X ⨿ Y) ≫ ((e X Y).hom ≫ binaryCoproductMap C f g) := by
          rw [← Category.assoc, heL]
    · calc
        (coprod.inr : Y ⟶ X ⨿ Y) ≫ (coprod.map f g ≫ (e X' Y').hom) =
            g ≫ ((coprod.inr : Y' ⟶ X' ⨿ Y') ≫ (e X' Y').hom) := by
          rw [← Category.assoc, coprod.inr_map, Category.assoc]
        _ = g ≫ c'.inr := by rw [heR]
        _ = c.inr ≫ binaryCoproductMap C f g := (binaryCoproductMap_inr C f g).symm
        _ = (coprod.inr : Y ⟶ X ⨿ Y) ≫ ((e X Y).hom ≫ binaryCoproductMap C f g) := by
          rw [← Category.assoc, heR]
  exact hstd.of_iso (e X₀ Y₀) (e X₁ Y₁) (e X₂ Y₂) (e X₃ Y₃)
    (hm t₀ t₁) (hm l₀ l₁) (hm r₀ r₁) (hm b₀ b₁)

/-- Every existing product-category pushout is preserved by the actual
derived coproduct functor, through the proved whole map transports. -/
theorem waldhausenCoproductFunctor_map_isPushout {X Y Z P : C × C}
    (f : X ⟶ Y) (g : X ⟶ Z) (inl : Y ⟶ P) (inr : Z ⟶ P)
    (hp : IsPushout f g inl inr) :
    IsPushout ((waldhausenCoproductFunctor C).map f) ((waldhausenCoproductFunctor C).map g)
      ((waldhausenCoproductFunctor C).map inl) ((waldhausenCoproductFunctor C).map inr) := by
  have hparts := (isPushout_prod_iff (C := C) (D := C)).mp hp
  have hraw := binaryCoproductMap_isPushout C f.1 f.2 g.1 g.2 inl.1 inl.2 inr.1 inr.2
    hparts.1 hparts.2
  let e (p : C × C) : (binaryCoproductColimitCocone C (pair p.1 p.2)).cocone.pt ≅
      (waldhausenCoproductFunctor C).obj p :=
    (eqToIso (waldhausenCoproductFunctor_obj C p)).symm
  have hm {p q : C × C} (φ : p ⟶ q) :
      binaryCoproductMap C φ.1 φ.2 ≫ (e q).hom =
        (e p).hom ≫ (waldhausenCoproductFunctor C).map φ := by
    let ep := eqToIso (waldhausenCoproductFunctor_obj C p)
    let eq := eqToIso (waldhausenCoproductFunctor_obj C q)
    change binaryCoproductMap C φ.1 φ.2 ≫ eq.inv =
      ep.inv ≫ (waldhausenCoproductFunctor C).map φ
    have hmap : (waldhausenCoproductFunctor C).map φ =
        ep.hom ≫ binaryCoproductMap C φ.1 φ.2 ≫ eq.inv :=
      waldhausenCoproductFunctor_map C φ
    rw [hmap]
    simp only [Iso.inv_hom_id_assoc]
  exact hraw.of_iso (e X) (e Y) (e Z) (e P) (hm f) (hm g) (hm inl) (hm inr)

end CategoryTheory.Waldhausen
