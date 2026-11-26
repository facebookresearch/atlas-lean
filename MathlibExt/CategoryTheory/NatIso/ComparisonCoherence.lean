/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado

module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Transport of categorical comparison identities

Natural isomorphisms transfer identity and composition equations between compatible functor
families. Coordinate isomorphisms also transfer morphism squares, inverse formulas, and
equality presentations.

These statements use arbitrary categories and the specified morphism and natural-isomorphism
equations. They retain the directions of each comparison and its inverse.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

open CategoryTheory

namespace CategoryTheory

/-- Compatible comparison transfers an identity equation.

If a natural comparison intertwines two identity-index transformations, normalization of the
first by an identity-functor isomorphism implies normalization of the second. -/
theorem comparison_identity {A D : Type*} [Category A] [Category D]
    {F H : A ⥤ D} (c : F ≅ H) (L : A ⥤ A) (e : L ≅ 𝟭 A)
    (a : F ⟶ L ⋙ F) (b : H ⟶ L ⋙ H)
    (hc : a ≫ Functor.whiskerLeft L c.hom = c.hom ≫ b)
    (ha : a ≫ Functor.whiskerRight e.hom F = 𝟙 F) :
    b ≫ Functor.whiskerRight e.hom H = 𝟙 H := by
  apply (cancel_epi c.hom).mp
  have hn := Functor.whiskerLeft_comp_whiskerRight e.hom c.hom
  calc
    _ = (c.hom ≫ b) ≫ Functor.whiskerRight e.hom H := (Category.assoc _ _ _).symm
    _ = a ≫ Functor.whiskerLeft L c.hom ≫ Functor.whiskerRight e.hom H := by rw [← hc,
      Category.assoc]
    _ = a ≫ Functor.whiskerRight e.hom F ≫ c.hom := by
      rw [hn]
      rfl
    _ = _ := by rw [← Category.assoc, ha, Category.id_comp, Category.comp_id]

-- V1/V2 abstract categorical associativity must be proved explicitly, not used as definitional
-- equality.
/-- Compatible comparisons transfer composition equations.

Three natural comparisons intertwining two successive maps and their composite transfer the
stated functor-associator composition equation to the compared family. -/
theorem comparison_composition
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {FA HA : A ⥤ D} {FB HB : B ⥤ D} {FC HC : C ⥤ D}
    (cA : FA ≅ HA) (cB : FB ≅ HB) (cC : FC ≅ HC)
    (L₁ : A ⥤ B) (L₂ : B ⥤ C) (L : A ⥤ C) (e : L₁ ⋙ L₂ ≅ L)
    (a₁ : FA ⟶ L₁ ⋙ FB) (b₁ : HA ⟶ L₁ ⋙ HB)
    (a₂ : FB ⟶ L₂ ⋙ FC) (b₂ : HB ⟶ L₂ ⋙ HC)
    (a : FA ⟶ L ⋙ FC) (b : HA ⟶ L ⋙ HC)
    (h₁ : a₁ ≫ Functor.whiskerLeft L₁ cB.hom = cA.hom ≫ b₁)
    (h₂ : a₂ ≫ Functor.whiskerLeft L₂ cC.hom = cB.hom ≫ b₂)
    (h : a ≫ Functor.whiskerLeft L cC.hom = cA.hom ≫ b)
    (ha : a₁ ≫ Functor.whiskerLeft L₁ a₂ ≫
      (Functor.associator L₁ L₂ FC).inv ≫ Functor.whiskerRight e.hom FC = a) :
    b₁ ≫ Functor.whiskerLeft L₁ b₂ ≫
      (Functor.associator L₁ L₂ HC).inv ≫ Functor.whiskerRight e.hom HC = b := by
  apply NatTrans.ext
  funext Q
  apply (cancel_epi (cA.hom.app Q)).mp
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp]
  change cA.hom.app Q ≫ (b₁.app Q ≫ b₂.app (L₁.obj Q) ≫ HC.map (e.hom.app Q)) =
    cA.hom.app Q ≫ b.app Q
  have h₁Q := congrArg (fun f => f.app Q) h₁
  change a₁.app Q ≫ cB.hom.app (L₁.obj Q) = cA.hom.app Q ≫ b₁.app Q at h₁Q
  have h₂Q := congrArg (fun f => f.app (L₁.obj Q)) h₂
  change a₂.app (L₁.obj Q) ≫ cC.hom.app (L₂.obj (L₁.obj Q)) =
    cB.hom.app (L₁.obj Q) ≫ b₂.app (L₁.obj Q) at h₂Q
  have hQ := congrArg (fun f => f.app Q) h
  change a.app Q ≫ cC.hom.app (L.obj Q) = cA.hom.app Q ≫ b.app Q at hQ
  have haQ := congrArg (fun f => f.app Q) ha
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at haQ
  have haQ' : (a₁.app Q ≫ a₂.app (L₁.obj Q)) ≫ FC.map (e.hom.app Q) = a.app Q :=
    (Category.assoc _ _ _).trans haQ
  have hn := cC.hom.naturality (e.hom.app Q)
  change FC.map (e.hom.app Q) ≫ cC.hom.app (L.obj Q) =
    cC.hom.app (L₂.obj (L₁.obj Q)) ≫ HC.map (e.hom.app Q) at hn
  calc
    _ = ((cA.hom.app Q ≫ b₁.app Q) ≫ b₂.app (L₁.obj Q)) ≫ HC.map (e.hom.app Q) := by
      simp only [Category.assoc]
    _ = a₁.app Q ≫ cB.hom.app (L₁.obj Q) ≫ b₂.app (L₁.obj Q) ≫ HC.map (e.hom.app Q) := by
      simpa only [Category.assoc] using congrArg
        (fun z => (z ≫ b₂.app (L₁.obj Q)) ≫ HC.map (e.hom.app Q)) h₁Q.symm
    _ = a₁.app Q ≫ (a₂.app (L₁.obj Q) ≫ cC.hom.app (L₂.obj (L₁.obj Q))) ≫ HC.map (e.hom.app Q) := by
      simpa only [Category.assoc] using congrArg
        (fun z => a₁.app Q ≫ z ≫ HC.map (e.hom.app Q)) h₂Q.symm
    _ = (a₁.app Q ≫ a₂.app (L₁.obj Q)) ≫
        (FC.map (e.hom.app Q) ≫ cC.hom.app (L.obj Q)) := by
      simpa only [Category.assoc] using congrArg
        (fun z => (a₁.app Q ≫ a₂.app (L₁.obj Q)) ≫ z) hn.symm
    _ = a.app Q ≫ cC.hom.app (L.obj Q) := by rw [← Category.assoc, haQ']
    _ = _ := hQ

end CategoryTheory

end


section

open CategoryTheory

namespace CategoryTheory
/-- Equal isomorphisms give equal inverse composites.

Replacing both isomorphisms by equal ones preserves their composite with the second inverse. -/
theorem inverse_comp_iso_eq {C : Type*} [Category C] {X Y Z : C}
    (a a' : X ≅ Z) (b b' : Y ≅ Z) (ha : a = a') (hb : b = b') :
    a ≪≫ b.symm = a' ≪≫ b'.symm := by
  cases ha
  cases hb
  rfl
end CategoryTheory

end


section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- An inverse coordinate cancels after a triple composite.

A composite of three maps followed by an isomorphism inverse and then its forward map equals
the three-map composite. -/
theorem comp_three_iso_inv_hom {C : Type*} [Category C] {A B D E F : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ F) (i : E ≅ F) :
    (a ≫ b ≫ c ≫ i.inv) ≫ i.hom = a ≫ b ≫ c := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]


/-- Functor image of an inverse recovers a transported point.

If the functor image of an isomorphism sends `x` to `y`, the image of its inverse sends `y` to
`x`. -/
theorem Functor.map_iso_inv_point {C : Type*} [Category C] (F : C ⥤ Type u)
    {X Y : C} (i : X ≅ Y) (x : F.obj X) (y : F.obj Y) (h : F.map i.hom x = y) :
    F.map i.inv y = x := by
  have hb : F.map i.inv (F.map i.hom x) = x := by
    simpa only [Functor.mapIso_hom, Functor.mapIso_inv, types_comp_apply, types_id_apply] using
      types_congr_hom (F.mapIso i).hom_inv_id x
  exact (congrArg (fun t => F.map i.inv t) h).symm.trans hb

end CategoryTheory

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory
/-- Coordinate square determines the conjugated morphism.

A commutative square `a ≫ f.hom = e.hom ≫ b` gives `e.hom ≫ b ≫ f.inv = a`. -/
theorem rankIso_transport_map_eq {C : Type*} [Category C] {X Y X' Y' : C}
    (e : X ≅ Y) (f : X' ≅ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : a ≫ f.hom = e.hom ≫ b) : e.hom ≫ b ≫ f.inv = a := by
  rw [← Category.assoc, ← h, Category.assoc, f.hom_inv_id, Category.comp_id]
end CategoryTheory

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory
/-- Inverse coordinate recovers a compatible morphism.

If `e.hom ≫ b = a`, then `e.inv ≫ a = b`. -/
theorem rankIso_inv_zero {C : Type*} [Category C] {X Y Z : C}
    (e : X ≅ Y) (a : X ⟶ Z) (b : Y ⟶ Z) (h : e.hom ≫ b = a) :
    e.inv ≫ a = b := by
  rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]
end CategoryTheory

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory
/-- A point coordinate remains compatible after a functor map.

A map into a source functor object agreeing with its comparison coordinate stays compatible
after the functor image of a morphism. -/
theorem postcompose_natural_zero {B D : Type*} [Category B] [Category D]
    (F I : B ⥤ D) (z : F ≅ I) {M N : B} (τ : M ⟶ N) {X : D}
    (g : X ⟶ F.obj M) (r : X ⟶ I.obj M) (h : g ≫ z.hom.app M = r) :
    (g ≫ F.map τ) ≫ z.hom.app N = r ≫ I.map τ :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun a => g ≫ a) (z.hom.naturality τ)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ I.map τ) h)))
end CategoryTheory

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory


/-- Two normalized coordinate systems give the same morphism square.

Compatible endpoint normalizations and two squares through a common target map give the
conjugated comparison square. -/
theorem normalized_conjugate_map {C : Type*} [Category C]
    {X Y A B V W I J : C}
    (e : X ≅ A) (f : Y ≅ B) (zX : X ≅ V) (zY : Y ≅ W)
    (g : V ≅ I) (h : W ≅ J) (nA : A ≅ I) (nB : B ≅ J)
    (a : V ⟶ W) (b : A ⟶ B) (r : I ⟶ J)
    (hc : e.hom ≫ nA.hom = zX.hom ≫ g.hom)
    (hd : f.hom ≫ nB.hom = zY.hom ≫ h.hom)
    (hb : b ≫ nB.hom = nA.hom ≫ r)
    (ha : a ≫ h.hom = g.hom ≫ r) :
    (e.hom ≫ b ≫ f.inv) ≫ zY.hom = zX.hom ≫ a := by
  apply (cancel_mono h.hom).mp
  have hi := rankIso_inv_zero f (zY.hom ≫ h.hom) nB.hom hd
  calc
    _ = e.hom ≫ b ≫ (f.inv ≫ (zY.hom ≫ h.hom)) := by simp only [Category.assoc]
    _ = e.hom ≫ b ≫ nB.hom := congrArg (fun a => e.hom ≫ b ≫ a) hi
    _ = e.hom ≫ (nA.hom ≫ r) := by rw [hb]
    _ = (zX.hom ≫ g.hom) ≫ r := by rw [← Category.assoc, hc]
    _ = _ := by rw [Category.assoc, ← ha]; exact (Category.assoc _ _ _).symm

/-- Conjugated morphism satisfies its coordinate square.

If `e.hom ≫ b ≫ f.inv = a`, then `a ≫ f.hom = e.hom ≫ b`. -/
theorem conjugate_map_square {C : Type*} [Category C] {X Y A B : C}
    (e : X ≅ A) (f : Y ≅ B) (b : A ⟶ B) (a : X ⟶ Y)
    (h : e.hom ≫ b ≫ f.inv = a) : a ≫ f.hom = e.hom ≫ b := by
  rw [← h, Category.assoc, Category.assoc, f.inv_hom_id, Category.comp_id]
end CategoryTheory

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory
/-- Isomorphism formulas transfer through stated equalities.

Equal comparison isomorphisms and equal factors preserve the displayed forward-map
factorization. -/
theorem mapped_formula_equalities {C : Type*} [Category C] {X Y Z : C}
    (e e' : X ≅ Y) (a a' : X ≅ Z) (b b' : Y ≅ Z)
    (he : e = e') (ha : a = a') (hb : b = b') (h : e'.hom = a'.hom ≫ b'.inv) :
    e.hom = a.hom ≫ b.inv := by cases he; cases ha; cases hb; exact h
end CategoryTheory

end

section

namespace CategoryTheory

/-- Morphism equality transports a commutative square.

Replacing either side map by an equal map preserves the commutative square with the fixed
other two maps. -/
theorem connector_equality_transport {C : Type*} [Category C]
    {A B D E : C} (d d' : A ⟶ B) (e e' : D ⟶ E)
    (f : B ⟶ E) (g : A ⟶ D)
    (hd : d = d') (he : e = e') (h : d' ≫ f = g ≫ e') :
    d ≫ f = g ≫ e := by
  cases hd
  cases he
  exact h

end CategoryTheory

end
