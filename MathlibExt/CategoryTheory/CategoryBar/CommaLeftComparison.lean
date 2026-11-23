/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryBar.ElementsNaturality
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# Left-comma comparison for simplicial replacement

For `F : C ⥤ D` and `d : D`, the covariant hom coefficient `commaCoeffL F d`
sends `c` to `d ⟶ F.obj c`. Its category of elements is explicitly equivalent
to the left comma category `StructuredArrow d F`, and simplicial replacement
at this coefficient is isomorphic to the nerve of that comma category via the
accepted elements comparison.

References (orientation only; no exact proposition correspondence is claimed):
nLab `comma category` page (https://ncatlab.org/nlab/show/comma+category);
Thomason, *Homotopy colimits in the category of small categories*
(https://doi.org/10.1017/S0305004100055535), for comma-fibre background.

Source-to-Lean map: the classical left comma category `d ↓ F` is Mathlib's
`StructuredArrow d F`; the representable coefficient is `commaCoeffL F d`, and
simplicial replacement at it compares via `commaReplacementNerveIso` against
`nerve (StructuredArrow d F)`.

Nonclaims: no right comma, no general Grothendieck equivalence, no
opposite/reversal comparison, no contraction, no homotopy, and no KQ statement.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u₁ v₁ u₂ v₂

namespace CategoryTheory

namespace CategoryBar

/-- Covariant hom coefficient for the left comma category. -/
noncomputable def commaCoeffL
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) : C ⥤ Type v₂ :=
  F ⋙ coyoneda.obj (op d)

@[simp] theorem commaCoeffL_obj
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) (c : C) :
    (commaCoeffL F d).obj c = (d ⟶ F.obj c) :=
  rfl

@[simp] theorem commaCoeffL_map
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) {c c' : C} (f : c ⟶ c') (h : d ⟶ F.obj c) :
    (commaCoeffL F d).map f h = h ≫ F.map f :=
  rfl

/-- Coefficient map induced by precomposition with `g : d ⟶ d'`. -/
noncomputable def commaCoeffLMap
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {d d' : D} (g : d ⟶ d') :
    commaCoeffL F d' ⟶ commaCoeffL F d :=
  Functor.whiskerLeft F (coyoneda.map g.op)

set_option backward.isDefEq.respectTransparency.types false in
/-- The category of elements of the left-comma coefficient is the comma category. -/
noncomputable def commaElementsEquivL
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) :
    (commaCoeffL F d).Elements ≌ StructuredArrow d F where
  functor :=
    { obj := fun X => StructuredArrow.mk X.val
      map := fun {X Y} f => StructuredArrow.homMk f.hom f.map_val }
  inverse :=
    { obj := fun X => (commaCoeffL F d).elementsMk X.right X.hom
      map := fun {X Y} f =>
        Functor.Elements.homMk f.right (StructuredArrow.w f) }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp X := by simp

/-- Degreewise nerve equivalence through the left-comma equivalence. -/
noncomputable def commaElementsNerveEquiv
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) (n : ℕ) :
    ComposableArrows (commaCoeffL F d).Elements n ≃
      ComposableArrows (StructuredArrow d F) n where
  toFun G :=
    { obj := fun i => StructuredArrow.mk (G.obj i).val
      map := fun {i j} f => StructuredArrow.homMk (G.map f).hom (G.map f).map_val
      map_id := fun i => by
        apply StructuredArrow.hom_ext _ _
        change (G.map (𝟙 i)).hom = 𝟙 (StructuredArrow.mk (G.obj i).val).right
        rw [G.map_id]
        rfl
      map_comp := fun f g => by
        apply StructuredArrow.hom_ext _ _
        change (G.map (f ≫ g)).hom =
          (G.map f).hom ≫ (G.map g).hom
        rw [G.map_comp]
        rfl }
  invFun G :=
    { obj := fun i => (commaCoeffL F d).elementsMk (G.obj i).right (G.obj i).hom
      map := fun {i j} f =>
        Functor.Elements.homMk (G.map f).right (StructuredArrow.w (G.map f))
      map_id := fun i => by
        apply Functor.Elements.hom_ext
        change (G.map (𝟙 i)).right = 𝟙 (G.obj i).right
        rw [G.map_id]
        rfl
      map_comp := fun f g => by
        apply Functor.Elements.hom_ext
        change (G.map (f ≫ g)).right =
          (G.map f).right ≫ (G.map g).right
        rw [G.map_comp]
        rfl }
  left_inv G := by
    refine Functor.ext (fun i => rfl) (fun i j f => ?_)
    · apply Functor.Elements.hom_ext
      change (G.map f).hom = 𝟙 _ ≫ (G.map f).hom ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
  right_inv G := by
    refine Functor.ext (fun i => ?_) (fun i j f => ?_)
    · refine StructuredArrow.obj_ext _ _ rfl ?_
      simp
    · apply StructuredArrow.hom_ext _ _
      have hEq : ∀ {x y : StructuredArrow d F} (h : x = y),
          (eqToHom h).right = eqToHom (congrArg StructuredArrow.right h) := by
        intro x y h
        cases h
        rfl
      rw [StructuredArrow.comp_right, StructuredArrow.comp_right, hEq, hEq]
      change (G.map f).right = 𝟙 _ ≫ (G.map f).right ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]

/-- Nerve-level isomorphism induced by the left-comma equivalence. -/
noncomputable def commaElementsNerveIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) :
    nerve (commaCoeffL F d).Elements ≅ nerve (StructuredArrow d F) :=
  NatIso.ofComponents (fun Δ => (commaElementsNerveEquiv F d (Δ.unop.len)).toIso) (by
    intro Δ₁ Δ₂ f
    ext X
    rfl)

@[simp] theorem commaElementsNerveIso_hom
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) :
    (commaElementsNerveIso F d).hom =
      nerveMap (commaElementsEquivL F d).functor :=
  rfl

@[simp] theorem commaElementsNerveIso_inv
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) :
    (commaElementsNerveIso F d).inv =
      nerveMap (commaElementsEquivL F d).inverse :=
  rfl

/-- Simplicial replacement at the left-comma coefficient is the comma nerve. -/
noncomputable def commaReplacementNerveIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) :
    simplicialReplacement (commaCoeffL F d) ≅ nerve (StructuredArrow d F) :=
  (replNerveSimplicialIso _).trans (commaElementsNerveIso F d)

/-- The left-comma replacement comparison is contravariantly natural in the comma point. -/
theorem commaReplacementNerve_naturality_d
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {d d' : D} (g : d ⟶ d') :
    replMap (commaCoeffLMap F g) ≫ (commaReplacementNerveIso F d).hom =
      (commaReplacementNerveIso F d').hom ≫ nerveMap (StructuredArrow.map g) := by
  have hSq :
      (commaCoeffLMap F g).mapElements ⋙
        (commaElementsEquivL F d).functor =
      (commaElementsEquivL F d').functor ⋙ StructuredArrow.map g := by
    have h_obj : ∀ X : (commaCoeffL F d').Elements,
        ((commaCoeffLMap F g).mapElements ⋙
          (commaElementsEquivL F d).functor).obj X =
        ((commaElementsEquivL F d').functor ⋙ StructuredArrow.map g).obj X :=
      fun X => rfl
    refine Functor.ext h_obj (fun X Y f => ?_)
    · apply StructuredArrow.hom_ext _ _
      have hEq : ∀ {x y : StructuredArrow d F} (h : x = y),
          (eqToHom h).right = eqToHom (congrArg StructuredArrow.right h) := by
        intro x y h
        cases h
        rfl
      rw [StructuredArrow.comp_right, StructuredArrow.comp_right, hEq, hEq]
      change (((commaCoeffLMap F g).mapElements ⋙
        (commaElementsEquivL F d).functor).map f).right =
        𝟙 _ ≫ (((commaElementsEquivL F d').functor ⋙
          StructuredArrow.map g).map f).right ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
      rfl
  have hNerveCompL :
      nerveMap ((commaCoeffLMap F g).mapElements ⋙
        (commaElementsEquivL F d).functor) =
      nerveMap (commaCoeffLMap F g).mapElements ≫
        nerveMap (commaElementsEquivL F d).functor := rfl
  have hNerveCompR :
      nerveMap ((commaElementsEquivL F d').functor ⋙ StructuredArrow.map g) =
      nerveMap (commaElementsEquivL F d').functor ≫
        nerveMap (StructuredArrow.map g) := rfl
  unfold commaReplacementNerveIso
  rw [Iso.trans_hom, Iso.trans_hom, commaElementsNerveIso_hom,
    commaElementsNerveIso_hom]
  rw [← Category.assoc, replNerve_naturality, Category.assoc, Category.assoc]
  rw [← hNerveCompL, ← hNerveCompR, hSq]

end CategoryBar

end CategoryTheory
