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

public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.FintypeCat

/-!
# Symmetric collections

Symmetric collections as functors from the groupoid of finite sets and bijections.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe v u

/-- The groupoid of finite types and bijections. -/
abbrev FinBijGroupoid := Core FintypeCat.{0}

namespace FinBijGroupoid

/-- The equivalence of underlying finite types represented by a morphism in the finite-bijection
groupoid. -/
def equivOfHom {X Y : FinBijGroupoid} (f : X ⟶ Y) : X.of ≃ Y.of :=
  FintypeCat.equivEquivIso.symm f.iso

/-- The morphism in the finite-bijection groupoid represented by an equivalence of finite types. -/
def homOfEquiv {X Y : FintypeCat} (e : X ≃ Y) :
    (⟨X⟩ : FinBijGroupoid) ⟶ ⟨Y⟩ :=
  (Core.isoMk (FintypeCat.equivEquivIso e)).hom

/-- The inverse of a morphism in the finite-bijection groupoid. -/
def inverse {X Y : FinBijGroupoid} (f : X ⟶ Y) : Y ⟶ X :=
  Groupoid.inv f

@[simp]
theorem equivOfHom_id (X : FinBijGroupoid) :
    equivOfHom (𝟙 X) = Equiv.refl X.of := by
  ext x
  rfl

@[simp]
theorem equivOfHom_comp {X Y Z : FinBijGroupoid} (f : X ⟶ Y) (g : Y ⟶ Z) :
    equivOfHom (f ≫ g) = (equivOfHom f).trans (equivOfHom g) := by
  ext x
  rfl

@[simp]
theorem equivOfHom_inv {X Y : FinBijGroupoid} (f : X ⟶ Y) :
    equivOfHom (inverse f) = (equivOfHom f).symm := by
  ext y
  rfl

@[simp]
theorem equivOfHom_homOfEquiv {X Y : FintypeCat} (e : X ≃ Y) :
    equivOfHom (homOfEquiv e) = e := by
  ext x
  rfl

@[simp]
theorem homOfEquiv_refl (X : FintypeCat) :
    homOfEquiv (Equiv.refl X) = 𝟙 (⟨X⟩ : FinBijGroupoid) := by
  apply Core.hom_ext
  apply FintypeCat.hom_ext
  intro x
  rfl

@[simp]
theorem homOfEquiv_trans {X Y Z : FintypeCat} (e : X ≃ Y) (f : Y ≃ Z) :
    homOfEquiv (e.trans f) = homOfEquiv e ≫ homOfEquiv f := by
  apply Core.hom_ext
  apply FintypeCat.hom_ext
  intro x
  rfl

@[simp]
theorem homOfEquiv_equivOfHom {X Y : FinBijGroupoid} (f : X ⟶ Y) :
    homOfEquiv (equivOfHom f) = f := by
  apply Core.hom_ext
  apply FintypeCat.hom_ext
  intro x
  rfl

end FinBijGroupoid

/-- Symmetric collections in a category `C`. -/
abbrev SymmetricCollection (C : Type u) [Category.{v} C] := FinBijGroupoid ⥤ C

variable {C : Type u} [Category.{v} C]

namespace SymmetricCollection

/-- Evaluation at a bundled finite type. -/
abbrev eval (X : SymmetricCollection C) (A : FintypeCat) : C :=
  X.obj ⟨A⟩

/-- Evaluation at `Fin n`. -/
abbrev evalFin (X : SymmetricCollection C) (n : ℕ) : C :=
  X.eval (FintypeCat.of (Fin n))

/-- The isomorphism on evaluations induced by an isomorphism of finite types. -/
def relabelIsoIso (X : SymmetricCollection C) {A B : FintypeCat} (i : A ≅ B) :
    X.eval A ≅ X.eval B :=
  X.mapIso (Core.isoMk i)

/-- The isomorphism on evaluations induced by an equivalence of finite types. -/
def relabelEquivIso (X : SymmetricCollection C) {A B : FintypeCat} (e : A ≃ B) :
    X.eval A ≅ X.eval B :=
  X.relabelIsoIso (FintypeCat.equivEquivIso e)

/-- Relabeling along an isomorphism of finite types. -/
def relabelIso (X : SymmetricCollection C) {A B : FintypeCat} (i : A ≅ B) :
    X.eval A ⟶ X.eval B :=
  X.map (Core.isoMk i).hom

/-- Relabeling along an equivalence of finite types. -/
def relabelEquiv (X : SymmetricCollection C) {A B : FintypeCat} (e : A ≃ B) :
    X.eval A ⟶ X.eval B :=
  X.relabelIso (FintypeCat.equivEquivIso e)

@[simp]
theorem relabelIsoIso_hom (X : SymmetricCollection C) {A B : FintypeCat} (i : A ≅ B) :
    (X.relabelIsoIso i).hom = X.relabelIso i :=
  rfl

@[simp]
theorem relabelEquivIso_hom (X : SymmetricCollection C) {A B : FintypeCat} (e : A ≃ B) :
    (X.relabelEquivIso e).hom = X.relabelEquiv e :=
  rfl

@[simp]
theorem relabelIso_refl (X : SymmetricCollection C) (A : FintypeCat) :
    X.relabelIso (Iso.refl A) = 𝟙 (X.eval A) := by
  unfold relabelIso
  have h : (Core.isoMk (Iso.refl A)).hom = 𝟙 (⟨A⟩ : Core FintypeCat) := rfl
  rw [h, X.map_id]

theorem relabelIso_trans (X : SymmetricCollection C) {A B C' : FintypeCat}
    (i : A ≅ B) (j : B ≅ C') :
    X.relabelIso (i ≪≫ j) = X.relabelIso i ≫ X.relabelIso j := by
  unfold relabelIso
  have h : (Core.isoMk (i ≪≫ j)).hom =
      (Core.isoMk i).hom ≫ (Core.isoMk j).hom := rfl
  rw [h, X.map_comp]

@[simp]
theorem relabelEquiv_refl (X : SymmetricCollection C) (A : FintypeCat) :
    X.relabelEquiv (Equiv.refl A) = 𝟙 (X.eval A) := by
  unfold relabelEquiv
  have h : FintypeCat.equivEquivIso (Equiv.refl A) = Iso.refl A := by
    ext x
    rfl
  rw [h, relabelIso_refl]

theorem relabelEquiv_trans (X : SymmetricCollection C) {A B C' : FintypeCat}
    (e : A ≃ B) (f : B ≃ C') :
    X.relabelEquiv (e.trans f) = X.relabelEquiv e ≫ X.relabelEquiv f := by
  unfold relabelEquiv
  have h : FintypeCat.equivEquivIso (e.trans f) =
      FintypeCat.equivEquivIso e ≪≫ FintypeCat.equivEquivIso f := by
    ext x
    rfl
  rw [h, relabelIso_trans]

end SymmetricCollection

end CategoryTheory.Operad
