/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Whiskering

/-!
# Iteration of endofunctors and intertwining transformations

The construction `iterate F n` composes an endofunctor with itself, starting
from the identity functor, and preserves every object property preserved by
`F`. A natural transformation `τ : G ⋙ F ⟶ F ⋙ H` induces a comparison
`iterate G n ⋙ F ⟶ F ⋙ iterate H n`. Its zero component is the identity,
and each successor component is the corresponding component of `τ`
followed by `H` applied to the preceding comparison.
-/

@[expose] public section

set_option autoImplicit false
universe u v
open CategoryTheory

namespace CategoryTheory.Functor.Iteration
variable {C : Type u} [Category.{v} C]

/-- Iterate the entire supplied endofunctor, retaining all maps and category laws. -/
def iterate (F : C ⥤ C) : ℕ → (C ⥤ C) :=
  Nat.rec (𝟭 C) (fun _ previous => previous ⋙ F)

/-- The whole successor map is the original functor applied to the preceding whole map. -/
theorem map_succ (F : C ⥤ C) (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (iterate F (n + 1)).map f = F.map ((iterate F n).map f) := rfl

/-- A proved object property is preserved at every genuine endofunctor iteration. -/
theorem preserves (F : C ⥤ C) (P : C → Prop) (hF : ∀ X, P X → P (F.obj X))
    (n : ℕ) (X : C) (hX : P X) : P ((iterate F n).obj X) := by
  induction n with
  | zero => exact hX
  | succ n ih => exact hF ((iterate F n).obj X) ih

universe uD vD

variable {D : Type uD} [Category.{vD} D] {G : C ⥤ C} {H : D ⥤ D} {F : C ⥤ D}

/-- The original comparison recursively constructs the actual comparison for every coordinate power. -/
def comparison (τ : G ⋙ F ⟶ F ⋙ H) : ∀ n, iterate G n ⋙ F ⟶ F ⋙ iterate H n
  | 0 => F.leftUnitor.hom ≫ F.rightUnitor.inv
  | n + 1 =>
    (Functor.associator (iterate G n) G F).hom ≫
      Functor.whiskerLeft (iterate G n) τ ≫
        (Functor.associator (iterate G n) F H).inv ≫
          Functor.whiskerRight (comparison τ n) H ≫
            (Functor.associator F (iterate H n) H).hom

/-- The zero comparison is the actual identity coefficient map. -/
theorem comparison_zero (τ : G ⋙ F ⟶ F ⋙ H) (A : C) :
    (comparison τ 0).app A = 𝟙 (F.obj A) := by
  dsimp [comparison, iterate, Functor.whiskerLeft, Functor.whiskerRight]
  simp

/-- Each successor comparison retains the original component and the actual target-coordinate map. -/
theorem comparison_succ (τ : G ⋙ F ⟶ F ⋙ H) (n : ℕ) (A : C) :
    (comparison τ (n + 1)).app A =
      τ.app ((iterate G n).obj A) ≫ H.map ((comparison τ n).app A) := by
  dsimp [comparison, iterate, Functor.whiskerLeft, Functor.whiskerRight]
  simp only [Category.id_comp, Category.comp_id]

/-- The first original iterated comparison is the original arbitrary comparison component. -/
theorem comparison_one (τ : G ⋙ F ⟶ F ⋙ H) (A : C) :
    (comparison τ 1).app A = τ.app A := by
  have h := comparison_succ τ 0 A
  change (comparison τ 1).app A = τ.app A ≫ H.map ((comparison τ 0).app A) at h
  have hz := comparison_zero τ A
  exact h.trans ((congrArg (fun f => τ.app A ≫ H.map f) hz).trans
    ((congrArg (fun f => τ.app A ≫ f) (H.map_id (F.obj A))).trans (Category.comp_id _)))

end CategoryTheory.Functor.Iteration
