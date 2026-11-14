/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-! # The cochain complex of a single arrow

This completed constructor uses the actual Mathlib cochain differential.
It is useful for connection de Rham complexes on curves.
-/

@[expose] public noncomputable section

namespace MathlibExt.Algebra.Homology

open CategoryTheory CategoryTheory.Limits ZeroObject

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  {A B : C}

/-- Place an actual arrow in degrees zero and one, with zero later terms. -/
def twoTermComplex (f : A ⟶ B) : CochainComplex C ℕ :=
  let X : ℕ → C := fun n ↦ match n with
    | 0 => A
    | 1 => B
    | _ + 2 => 0
  let d : ∀ n, X n ⟶ X (n + 1) := fun n ↦ match n with
    | 0 => f
    | _ + 1 => 0
  CochainComplex.of X d (fun n ↦ by cases n <;> simp [d])

@[simp] theorem twoTermComplex_X_zero (f : A ⟶ B) : (twoTermComplex f).X 0 = A := rfl

@[simp] theorem twoTermComplex_X_one (f : A ⟶ B) : (twoTermComplex f).X 1 = B := rfl

@[simp] theorem twoTermComplex_d_zero (f : A ⟶ B) : (twoTermComplex f).d 0 1 = f := by
  dsimp [twoTermComplex]
  apply CochainComplex.of_d

end MathlibExt.Algebra.Homology
