/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.SumRelCat
import MathlibExt.CategoryTheory.Monoidal.RelCat

open CategoryTheory MonoidalCategory Limits
open scoped MonoidalCategory

universe u

-- Both relational tensors coexist, with no finiteness or nonemptiness assumptions.
example : CartesianMonoidalCategory SumRelCat.{u} := inferInstance
example : SymmetricCategory SumRelCat.{u} := inferInstance
example : HasFiniteProducts SumRelCat.{u} := inferInstance
example : HasFiniteCoproducts SumRelCat.{u} := inferInstance
example (X Y : SumRelCat.{u}) : X ⊗ Y = SumRelCat.sum X Y := rfl
example (X Y : RelCat.{u}) : X ⊗ Y = (X × Y : RelCat) := rfl
example : 𝟙_ SumRelCat.{u} = (SumRelCat.of PEmpty) := rfl
example : 𝟙_ RelCat.{u} = (PUnit : RelCat) := rfl
example : IsTerminal (SumRelCat.zero : SumRelCat.{u}) := SumRelCat.zeroIsTerminal
example : IsInitial (SumRelCat.zero : SumRelCat.{u}) := SumRelCat.zeroIsInitial

namespace SumRelTests
open SumRelCat
variable {X Y Z : SumRelCat.{u}}
-- Elementwise consumers work with default elaboration and simplifier options.
example (x y : X) : (Sum.inl x, y) ∈ (fst X Y).rel ↔ x = y := by simp
example (x : X) (y : Y) : (Sum.inr y, x) ∉ (fst X Y).rel := by simp
example (f : Z ⟶ X) (g : Z ⟶ Y) (z : Z) (x : X) :
    (z, Sum.inl x) ∈ (pair f g).rel ↔ (z, x) ∈ f.rel := by simp
example (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (z : Z) :
    (x, z) ∈ (f ≫ g).rel ↔ ∃ y, (x, y) ∈ f.rel ∧ (y, z) ∈ g.rel :=
  comp_rel f g x z
example (f : Z ⟶ X) (g : Z ⟶ Y) : pair f g ≫ fst X Y = f := by simp
example (f : Z ⟶ X) (g : Z ⟶ Y) : pair f g ≫ snd X Y = g := by simp
example (f : X ⟶ Z) (g : Y ⟶ Z) : inl X Y ≫ desc f g = f := by simp
example (f : X ⟶ Z) (g : Y ⟶ Z) : inr X Y ≫ desc f g = g := by simp
example {f g : Z ⟶ sum X Y} (h₁ : f ≫ fst X Y = g ≫ fst X Y)
    (h₂ : f ≫ snd X Y = g ≫ snd X Y) : f = g := SumRelCat.hom_ext h₁ h₂
example {f g : sum X Y ⟶ Z} (h₁ : inl X Y ≫ f = inl X Y ≫ g)
    (h₂ : inr X Y ≫ f = inr X Y ≫ g) : f = g := hom_ext_out h₁ h₂
example (X Y : SumRelCat.{u}) : IsLimit (binaryProduct X Y).cone :=
  (binaryProduct X Y).isLimit
example (X Y : SumRelCat.{u}) : IsColimit (binaryCoproduct X Y).cocone :=
  (binaryCoproduct X Y).isColimit
example (X Y Z : SumRelCat.{u}) (x : X) :
    (Sum.inl (Sum.inl x), Sum.inl x) ∈ (α_ X Y Z).hom.rel := by simp
example (X Y Z : SumRelCat.{u}) (y : Y) :
    (Sum.inl (Sum.inr y), Sum.inr (Sum.inl y)) ∈ (α_ X Y Z).hom.rel := by simp
example (X Y Z : SumRelCat.{u}) (z : Z) :
    (Sum.inr z, Sum.inr (Sum.inr z)) ∈ (α_ X Y Z).hom.rel := by simp
example (X Y Z : SumRelCat.{u}) (x : Sum X (Sum Y Z)) :
    (x, (Equiv.sumAssoc X Y Z).symm x) ∈ (α_ X Y Z).inv.rel := by simp
example (X Y : SumRelCat.{u}) (x : X) : (Sum.inl x, Sum.inr x) ∈ (β_ X Y).hom.rel := by simp
example (X Y : SumRelCat.{u}) (y : Y) : (Sum.inr y, Sum.inl y) ∈ (β_ X Y).hom.rel := by simp
example (X : SumRelCat.{u}) (x : X) : (Sum.inr x, x) ∈ (λ_ X).hom.rel := by simp
example (X : SumRelCat.{u}) (x : X) : (x, Sum.inr x) ∈ (λ_ X).inv.rel := by simp
example (X : SumRelCat.{u}) (x : X) : (Sum.inl x, x) ∈ (ρ_ X).hom.rel := by simp
example (X : SumRelCat.{u}) (x : X) : (x, Sum.inl x) ∈ (ρ_ X).inv.rel := by simp

private def branching : of Bool ⟶ of Bool := .ofRel {p | p.1 = false}
private def empty : of Bool ⟶ of Bool := .ofRel ∅

-- A single input can relate to both outputs; tensor preserves that nondeterminism.
example : (Sum.inl false, Sum.inl false) ∈ (branching ⊗ₘ empty).rel := by
  simp [branching]
example : (Sum.inl false, Sum.inl true) ∈ (branching ⊗ₘ empty).rel := by
  simp [branching]
example : (Sum.inl false, Sum.inr true) ∉ (branching ⊗ₘ branching).rel := by simp
example : (Sum.inr false, Sum.inl true) ∉ (branching ⊗ₘ branching).rel := by simp
example : (Sum.inr false, Sum.inr true) ∉ (branching ⊗ₘ empty).rel := by simp [empty]
example : (Sum.inr false, Sum.inr true) ∈ ((of Bool) ◁ branching).rel := by
  simp [branching]
example : (Sum.inl false, Sum.inl true) ∈ (branching ▷ (SumRelCat.of PEmpty)).rel := by
  simp [branching]
example : (Sum.inl false, Sum.inl true) ∈
    (branching ⊗ₘ (𝟙 (SumRelCat.of PEmpty))).rel := by
  simp [branching]
-- Pairing a branching relation with itself allows both summands as outputs.
example : (false, Sum.inl true) ∈ (pair branching branching).rel ∧
    (false, Sum.inr true) ∈ (pair branching branching).rel := by
  simp [branching]
example : (Sum.inl false, true) ∈ (desc branching branching).rel ∧
    (Sum.inr false, true) ∈ (desc branching branching).rel := by
  simp [branching]
end SumRelTests
