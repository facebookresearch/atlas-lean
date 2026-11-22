/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Sequential spectra in a monoidal category

A sequential spectrum with suspension coordinate `K` consists of objects `X n`
and left structure maps `K ⊗ X n ⟶ X (n + 1)`. Morphisms are level maps
commuting with these structure maps. Evaluation at a level is the literal
projection functor.
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory MonoidalCategory

namespace CategoryTheory

/-- A sequential spectrum in a monoidal category with suspension coordinate
`K`. -/
structure SequentialSpectrum (C : Type u) [Category.{v} C]
    [MonoidalCategory C] (K : C) where
  /-- The object in level `n`. -/
  level : ℕ → C
  /-- The left structure map from level `n` to level `n + 1`. -/
  structureMap (n : ℕ) : K ⊗ level n ⟶ level (n + 1)

namespace SequentialSpectrum

/-- A morphism of sequential spectra is a levelwise map commuting with the
left structure maps. -/
@[ext]
structure Hom {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {K : C} (X Y : SequentialSpectrum C K) where
  /-- The component in level `n`. -/
  levelMap (n : ℕ) : X.level n ⟶ Y.level n
  /-- Compatibility with the left structure maps. -/
  naturality (n : ℕ) :
    (K ◁ levelMap n) ≫ Y.structureMap n =
      X.structureMap n ≫ levelMap (n + 1)

/-- Sequential spectra and their levelwise morphisms form a category. -/
instance instCategory {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {K : C} : Category.{v} (SequentialSpectrum C K) where
  Hom := Hom
  id X :=
    { levelMap := fun _ => 𝟙 _
      naturality := by simp }
  comp f g :=
    { levelMap := fun n => f.levelMap n ≫ g.levelMap n
      naturality := by
        intro n
        rw [whiskerLeft_comp, Category.assoc, g.naturality]
        rw [← Category.assoc, f.naturality, Category.assoc] }
  id_comp := by
    intro X Y f
    ext n
    exact Category.id_comp _
  comp_id := by
    intro X Y f
    ext n
    exact Category.comp_id _
  assoc := by
    intro W X Y Z f g h
    ext n
    exact Category.assoc _ _ _

/-- Two sequential-spectrum morphisms are equal when all their level maps are
equal. -/
@[ext]
theorem hom_ext {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {K : C} {X Y : SequentialSpectrum C K} (f g : X ⟶ Y)
    (h : ∀ n, f.levelMap n = g.levelMap n) : f = g := by
  apply Hom.ext
  funext n
  exact h n

/-- Evaluation of a sequential spectrum at level `n`. -/
def evaluation {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (K : C) (n : ℕ) : SequentialSpectrum C K ⥤ C where
  obj X := X.level n
  map f := f.levelMap n
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Evaluation at `n` returns the level-`n` object. -/
@[simp]
theorem evaluation_obj {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (K : C) (n : ℕ) (X : SequentialSpectrum C K) :
    (evaluation K n).obj X = X.level n := rfl

/-- Evaluation at `n` returns the level-`n` map. -/
@[simp]
theorem evaluation_map {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (K : C) (n : ℕ) {X Y : SequentialSpectrum C K} (f : X ⟶ Y) :
    (evaluation K n).map f = f.levelMap n := rfl

end SequentialSpectrum
end CategoryTheory
