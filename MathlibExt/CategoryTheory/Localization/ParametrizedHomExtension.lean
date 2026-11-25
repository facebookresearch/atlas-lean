/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import Mathlib.CategoryTheory.Localization.HasLocalization
public import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Parametrized Hom adjunctions on three independent localizations

Actual Hom bijections on the original objects and naturality for the three
original arrow variables construct a complete parametrized adjunction on
the three canonical localized categories. The proof extends each naturality
equation through composition and the actual formal inverses. No model
category, weak factorization system or derived adjunction is an input.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u₁ u₂ u₃ v₁ v₂ v₃ u₀ v₀

open CategoryTheory Functor Opposite

namespace CategoryTheory.Localization.ParametrizedHomExtension

/-- The canonical localization of the original category at the specified morphism property. -/
abbrev Localized {C : Type u₀} [Category.{v₀} C] (W : MorphismProperty C) :=
  MorphismProperty.Localization W

/-- The canonical projection from the original category to its specified localization. -/
abbrev project {C : Type u₀} [Category.{v₀} C] (W : MorphismProperty C) : C ⥤ Localized W :=
  MorphismProperty.Q W

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃]
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)

variable (F : Localized W₁ ⥤ Localized W₂ ⥤ Localized W₃)
  (G : (Localized W₁)ᵒᵖ ⥤ Localized W₃ ⥤ Localized W₂)
  (nativeHom : ∀ (A : C₁) (B : C₂) (Z : C₃),
    ((F.obj ((project W₁).obj A)).obj ((project W₂).obj B) ⟶ (project W₃).obj Z) ≃
      ((project W₂).obj B ⟶ (G.obj (op ((project W₁).obj A))).obj ((project W₃).obj Z)))

/-- The same actual original Hom functions, on every canonical localization object. -/
def homEquiv (A : Localized W₁) (B : Localized W₂) (Z : Localized W₃) :
    ((F.obj A).obj B ⟶ Z) ≃ (B ⟶ (G.obj (op A)).obj Z) := by
  rcases A with ⟨⟨X⟩⟩
  rcases B with ⟨⟨Y⟩⟩
  rcases Z with ⟨⟨E⟩⟩
  exact nativeHom X Y E

private def sourceNaturality : MorphismProperty (Localized W₂) := fun B B' f =>
  ∀ (A : Localized W₁) (Z : Localized W₃) (g : (F.obj A).obj B' ⟶ Z),
    homEquiv W₁ W₂ W₃ F G nativeHom A B Z ((F.obj A).map f ≫ g) =
      f ≫ homEquiv W₁ W₂ W₃ F G nativeHom A B' Z g

private def targetNaturality : MorphismProperty (Localized W₃) := fun Z Z' f =>
  ∀ (A : Localized W₁) (B : Localized W₂) (g : (F.obj A).obj B ⟶ Z),
    homEquiv W₁ W₂ W₃ F G nativeHom A B Z' (g ≫ f) =
      homEquiv W₁ W₂ W₃ F G nativeHom A B Z g ≫ (G.obj (op A)).map f

private def parameterNaturality : MorphismProperty (Localized W₁) := fun A A' f =>
  ∀ (B : Localized W₂) (Z : Localized W₃) (g : (F.obj A').obj B ⟶ Z),
    homEquiv W₁ W₂ W₃ F G nativeHom A B Z ((F.map f).app B ≫ g) =
      homEquiv W₁ W₂ W₃ F G nativeHom A' B Z g ≫ (G.map f.op).app Z

private instance sourceNaturality_comp :
    (sourceNaturality W₁ W₂ W₃ F G nativeHom).IsStableUnderComposition where
  comp_mem f g hf hg A Z k := by
    rw [Functor.map_comp, Category.assoc, hf A Z, hg A Z, Category.assoc]

private instance targetNaturality_comp :
    (targetNaturality W₁ W₂ W₃ F G nativeHom).IsStableUnderComposition where
  comp_mem f g hf hg A B k := by
    rw [← Category.assoc, hg A B, hf A B, Functor.map_comp, Category.assoc]

private instance parameterNaturality_comp :
    (parameterNaturality W₁ W₂ W₃ F G nativeHom).IsStableUnderComposition where
  comp_mem f g hf hg B Z k := by
    rw [Functor.map_comp, NatTrans.comp_app, Category.assoc, hf B Z, hg B Z]
    change _ = homEquiv W₁ W₂ W₃ F G nativeHom _ B Z k ≫ (G.map (g.op ≫ f.op)).app Z
    rw [Functor.map_comp, NatTrans.comp_app, Category.assoc]

private theorem sourceNaturality_inverse {B B' : Localized W₂} (e : B ≅ B')
    (he : sourceNaturality W₁ W₂ W₃ F G nativeHom e.hom) :
    sourceNaturality W₁ W₂ W₃ F G nativeHom e.inv := by
  intro A Z k
  have h := he A Z ((F.obj A).map e.inv ≫ k)
  rw [← Category.assoc, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp] at h
  apply (cancel_epi e.hom).mp
  rw [← h, ← Category.assoc, e.hom_inv_id, Category.id_comp]

private theorem targetNaturality_inverse {Z Z' : Localized W₃} (e : Z ≅ Z')
    (he : targetNaturality W₁ W₂ W₃ F G nativeHom e.hom) :
    targetNaturality W₁ W₂ W₃ F G nativeHom e.inv := by
  intro A B k
  have h := he A B (k ≫ e.inv)
  rw [Category.assoc, e.inv_hom_id, Category.comp_id] at h
  apply (cancel_mono ((G.obj (op A)).map e.hom)).mp
  rw [← h, Category.assoc, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

private theorem parameterNaturality_inverse {A A' : Localized W₁} (e : A ≅ A')
    (he : parameterNaturality W₁ W₂ W₃ F G nativeHom e.hom) :
    parameterNaturality W₁ W₂ W₃ F G nativeHom e.inv := by
  intro B Z k
  have h := he B Z ((F.map e.inv).app B ≫ k)
  have hF : (F.map e.hom).app B ≫ (F.map e.inv).app B = 𝟙 _ := ((F.mapIso e).app B).hom_inv_id
  rw [← Category.assoc, hF, Category.id_comp] at h
  have hG : (G.map e.inv.op).app Z ≫ (G.map e.hom.op).app Z = 𝟙 _ :=
    ((G.mapIso e.op).app Z).inv_hom_id
  apply (cancel_mono ((G.map e.hom.op).app Z)).mp
  rw [← h, Category.assoc, hG, Category.comp_id]

variable
  (hSource : ∀ (A : C₁) {B B' : C₂} (f : B ⟶ B') (Z : C₃)
    (g : (F.obj ((project W₁).obj A)).obj ((project W₂).obj B') ⟶ (project W₃).obj Z),
      nativeHom A B Z ((F.obj ((project W₁).obj A)).map ((project W₂).map f) ≫ g) =
        (project W₂).map f ≫ nativeHom A B' Z g)
  (hTarget : ∀ (A : C₁) (B : C₂) {Z Z' : C₃} (f : Z ⟶ Z')
    (g : (F.obj ((project W₁).obj A)).obj ((project W₂).obj B) ⟶ (project W₃).obj Z),
      nativeHom A B Z' (g ≫ (project W₃).map f) =
        nativeHom A B Z g ≫ (G.obj (op ((project W₁).obj A))).map ((project W₃).map f))
  (hParameter : ∀ {A A' : C₁} (f : A ⟶ A') (B : C₂) (Z : C₃)
    (g : (F.obj ((project W₁).obj A')).obj ((project W₂).obj B) ⟶ (project W₃).obj Z),
      nativeHom A B Z ((F.map ((project W₁).map f)).app ((project W₂).obj B) ≫ g) =
        nativeHom A' B Z g ≫ (G.map ((project W₁).map f).op).app ((project W₃).obj Z))

include hSource in
private theorem sourceNaturality_original {X Y : C₂} (f : X ⟶ Y) :
    sourceNaturality W₁ W₂ W₃ F G nativeHom ((project W₂).map f) := by
  rintro ⟨⟨A⟩⟩ ⟨⟨Z⟩⟩ g
  exact hSource A f Z g

include hTarget in
private theorem targetNaturality_original {X Y : C₃} (f : X ⟶ Y) :
    targetNaturality W₁ W₂ W₃ F G nativeHom ((project W₃).map f) := by
  rintro ⟨⟨A⟩⟩ ⟨⟨B⟩⟩ g
  exact hTarget A B f g

include hParameter in
private theorem parameterNaturality_original {X Y : C₁} (f : X ⟶ Y) :
    parameterNaturality W₁ W₂ W₃ F G nativeHom ((project W₁).map f) := by
  rintro ⟨⟨B⟩⟩ ⟨⟨Z⟩⟩ g
  exact hParameter f B Z g

include hSource in
private theorem sourceNaturality_all : sourceNaturality W₁ W₂ W₃ F G nativeHom = ⊤ := by
  apply Construction.morphismProperty_eq_top
  · intro X Y f
    exact sourceNaturality_original W₁ W₂ W₃ F G nativeHom hSource f
  · intro X Y f hf
    exact sourceNaturality_inverse W₁ W₂ W₃ F G nativeHom (Construction.wIso f hf)
      (sourceNaturality_original W₁ W₂ W₃ F G nativeHom hSource f)

include hTarget in
private theorem targetNaturality_all : targetNaturality W₁ W₂ W₃ F G nativeHom = ⊤ := by
  apply Construction.morphismProperty_eq_top
  · intro X Y f
    exact targetNaturality_original W₁ W₂ W₃ F G nativeHom hTarget f
  · intro X Y f hf
    exact targetNaturality_inverse W₁ W₂ W₃ F G nativeHom (Construction.wIso f hf)
      (targetNaturality_original W₁ W₂ W₃ F G nativeHom hTarget f)

include hParameter in
private theorem parameterNaturality_all : parameterNaturality W₁ W₂ W₃ F G nativeHom = ⊤ := by
  apply Construction.morphismProperty_eq_top
  · intro X Y f
    exact parameterNaturality_original W₁ W₂ W₃ F G nativeHom hParameter f
  · intro X Y f hf
    exact parameterNaturality_inverse W₁ W₂ W₃ F G nativeHom (Construction.wIso f hf)
      (parameterNaturality_original W₁ W₂ W₃ F G nativeHom hParameter f)

include hSource in
/-- Actual source naturality extends to every localized second-variable arrow. -/
theorem homEquiv_naturality_source (A : Localized W₁) {B B' : Localized W₂} (f : B ⟶
  B') (Z : Localized W₃)
    (g : (F.obj A).obj B' ⟶ Z) :
    homEquiv W₁ W₂ W₃ F G nativeHom A B Z ((F.obj A).map f ≫ g) =
      f ≫ homEquiv W₁ W₂ W₃ F G nativeHom A B' Z g := by
  have h : sourceNaturality W₁ W₂ W₃ F G nativeHom f := by
    rw [sourceNaturality_all W₁ W₂ W₃ F G nativeHom hSource]; trivial
  exact h A Z g

include hTarget in
/-- Actual target naturality extends to every localized third-variable arrow. -/
theorem homEquiv_naturality_target (A : Localized W₁) (B : Localized W₂) {Z Z' :
  Localized W₃} (f : Z ⟶ Z')
    (g : (F.obj A).obj B ⟶ Z) :
    homEquiv W₁ W₂ W₃ F G nativeHom A B Z' (g ≫ f) =
      homEquiv W₁ W₂ W₃ F G nativeHom A B Z g ≫ (G.obj (op A)).map f := by
  have h : targetNaturality W₁ W₂ W₃ F G nativeHom f := by
    rw [targetNaturality_all W₁ W₂ W₃ F G nativeHom hTarget]; trivial
  exact h A B g

include hParameter in
/-- Actual parameter naturality extends to every localized first-variable arrow. -/
theorem homEquiv_naturality_parameter {A A' : Localized W₁} (f : A ⟶ A') (B : Localized
  W₂) (Z : Localized W₃)
    (g : (F.obj A').obj B ⟶ Z) :
    homEquiv W₁ W₂ W₃ F G nativeHom A B Z ((F.map f).app B ≫ g) =
      homEquiv W₁ W₂ W₃ F G nativeHom A' B Z g ≫ (G.map f.op).app Z := by
  have h : parameterNaturality W₁ W₂ W₃ F G nativeHom f := by
    rw [parameterNaturality_all W₁ W₂ W₃ F G nativeHom hParameter]; trivial
  exact h B Z g

/-- The actual original Hom functions construct the full adjunction at every localized parameter. -/
def adjunction (A : Localized W₁) : F.obj A ⊣ G.obj (op A) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv W₁ W₂ W₃ F G nativeHom A
      homEquiv_naturality_left_symm := by
        intro B' B Z f g
        apply (homEquiv W₁ W₂ W₃ F G nativeHom A B' Z).injective
        rw [Equiv.apply_symm_apply, homEquiv_naturality_source W₁ W₂ W₃ F G nativeHom hSource,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro B Z Z' f g
        exact homEquiv_naturality_target W₁ W₂ W₃ F G nativeHom hTarget A B g f }

/-- The complete adjunction retains the same actual Hom function. -/
theorem adjunction_homEquiv (A : Localized W₁) (B : Localized W₂) (Z : Localized W₃)
  (f : (F.obj A).obj B ⟶ Z) :
    (adjunction W₁ W₂ W₃ F G nativeHom hSource hTarget A).homEquiv B Z f =
      homEquiv W₁ W₂ W₃ F G nativeHom A B Z f := by
  rw [adjunction, Adjunction.mkOfHomEquiv_homEquiv]

/-- The source Hom functions and all three proved source naturalities construct the full
parametrized adjunction. -/
def parametrizedAdjunction : F ⊣₂ G :=
  ParametrizedAdjunction.mk' (adjunction W₁ W₂ W₃ F G nativeHom hSource hTarget) (by
    intro A A' f B Z g
    rw [adjunction_homEquiv, adjunction_homEquiv]
    exact homEquiv_naturality_parameter W₁ W₂ W₃ F G nativeHom hParameter f B Z g)

/-- Every represented original triple keeps its original actual Hom bijection. -/
theorem parametrizedAdjunction_source (A : C₁) (B : C₂) (Z : C₃)
    (f : (F.obj ((project W₁).obj A)).obj ((project W₂).obj B) ⟶ (project W₃).obj Z) :
    (parametrizedAdjunction W₁ W₂ W₃ F G nativeHom hSource hTarget hParameter).homEquiv f =
      nativeHom A B Z f := by
  change (adjunction W₁ W₂ W₃ F G nativeHom hSource hTarget ((project W₁).obj A)).homEquiv
    ((project W₂).obj B) ((project W₃).obj Z) f = _
  rw [adjunction_homEquiv]
  rfl

end CategoryTheory.Localization.ParametrizedHomExtension
