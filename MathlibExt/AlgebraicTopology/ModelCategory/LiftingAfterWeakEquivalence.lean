/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# Lifting after a weak equivalence

A lifting problem with a cofibration on the left and a fibration on the right has a solution
if and only if it has a solution after a weak equivalence of its lower left object, compatible
with the upper left object. The two diagonals in Bergner's proof come from the lifting axioms
for the given model structure.

## References

* Julia E. Bergner, *A model category structure on the category of simplicial categories*,
  Transactions of the American Mathematical Society 359 (2007), 2043–2058,
  Lemma 2.6; arXiv:math/0406507v2.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- A lift against a fibration exists exactly when it exists after a weak equivalence of
the lower left object compatible with the cofibration. Either existence assertion implies that the
outer square commutes, so a separate commutativity hypothesis is unnecessary. -/
theorem exists_lift_iff_of_weakEquivalence
    {A B B' X Y : C} (a : A ⟶ B) [Cofibration a] (a' : A ⟶ B')
    (f : A ⟶ X) (w : B' ⟶ B) [WeakEquivalence w]
    (r : X ⟶ Y) [Fibration r] (q : B ⟶ Y) (hcomm : a' ≫ w = a) :
    (∃ l : B ⟶ X, a ≫ l = f ∧ l ≫ r = q) ↔
      ∃ l' : B' ⟶ X, a' ≫ l' = f ∧ l' ≫ r = w ≫ q := by
  constructor
  · rintro ⟨l, hl, hr⟩
    exact ⟨w ≫ l, by simp only [← Category.assoc, hcomm, hl],
      by simp only [Category.assoc, hr]⟩
  · rintro ⟨l', hl, hr⟩
    let d := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) w
    have : Cofibration d.i := ⟨d.hi.1⟩
    have : WeakEquivalence d.i := ⟨d.hi.2⟩
    have : Fibration d.p := ⟨d.hp⟩
    have : WeakEquivalence d.p := weakEquivalence_of_precomp_of_fac d.fac
    let sq₁ : CommSq (a' ≫ d.i) a d.p (𝟙 B) :=
      ⟨by simpa only [Category.assoc, d.fac, Category.comp_id] using hcomm⟩
    let sq₂ : CommSq l' d.i r (d.p ≫ q) :=
      ⟨by simpa only [← Category.assoc, d.fac] using hr⟩
    refine ⟨sq₁.lift ≫ sq₂.lift, ?_, ?_⟩
    · calc
        a ≫ (sq₁.lift ≫ sq₂.lift) = (a ≫ sq₁.lift) ≫ sq₂.lift :=
          (Category.assoc _ _ _).symm
        _ = (a' ≫ d.i) ≫ sq₂.lift := by rw [sq₁.fac_left]
        _ = a' ≫ (d.i ≫ sq₂.lift) := Category.assoc _ _ _
        _ = f := by rw [sq₂.fac_left, hl]
    · calc
        (sq₁.lift ≫ sq₂.lift) ≫ r = sq₁.lift ≫ (sq₂.lift ≫ r) :=
          Category.assoc _ _ _
        _ = sq₁.lift ≫ (d.p ≫ q) := by rw [sq₂.fac_right]
        _ = (sq₁.lift ≫ d.p) ≫ q := (Category.assoc _ _ _).symm
        _ = q := by rw [sq₁.fac_right, Category.id_comp]

end HomotopicalAlgebra
