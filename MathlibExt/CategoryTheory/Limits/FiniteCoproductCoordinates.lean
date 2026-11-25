/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Limits.FiniteCoproductSuccessor
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# The actual zero/identity coordinates of a finite coproduct

Each coordinate is the original chosen coproduct descent of identity on
its own label and zero elsewhere. Successor splitting preserves the full
first coordinate and every original tail coordinate map.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.FiniteCoproductCoordinates

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasZeroMorphisms C]

/-- The whole original coordinate descent is identity on its label and zero on the other labels. -/
def coordinate {n : ℕ} (X : Fin n → C) (i : Fin n) : (∐ X) ⟶ X i :=
  Sigma.desc (fun j => if h : j = i then eqToHom (congrArg X h) else 0)

/-- The full original diagonal coordinate is the same identity map. -/
@[reassoc]
theorem coordinate_self {n : ℕ} (X : Fin n → C) (i : Fin n) :
    Sigma.ι X i ≫ coordinate X i = 𝟙 (X i) := by
  simp [coordinate]

/-- The full original off-diagonal coordinate is the same zero map. -/
@[reassoc]
theorem coordinate_ne {n : ℕ} (X : Fin n → C) (i j : Fin n) (h : j ≠ i) :
    Sigma.ι X j ≫ coordinate X i = 0 := by
  simp [coordinate, h]

/-- The first coordinate of the original successor split is the unchanged identity/zero
binary projection. -/
theorem first {n : ℕ} (X : Fin (n + 1) → C) :
    (FiniteCoproductSuccessor.iso X).hom ≫ coprod.desc (𝟙 (X 0)) 0 = coordinate X 0 := by
  apply Sigma.hom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [← Category.assoc, FiniteCoproductSuccessor.first_hom, coprod.inl_desc, coordinate_self]
  · rw [← Category.assoc, FiniteCoproductSuccessor.successor_hom, Category.assoc, coprod.inr_desc,
      comp_zero, coordinate_ne X 0 j.succ (Fin.succ_ne_zero j)]

/-- Every successor coordinate of the full original split is the unchanged tail coordinate. -/
theorem successor {n : ℕ} (X : Fin (n + 1) → C) (j : Fin n) :
    (FiniteCoproductSuccessor.iso X).hom ≫ coprod.desc 0 (𝟙 (∐ FiniteCoproductSuccessor.tail X)) ≫
      coordinate (FiniteCoproductSuccessor.tail X) j = coordinate X j.succ := by
  apply Sigma.hom_ext
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [← Category.assoc, ← Category.assoc, FiniteCoproductSuccessor.first_hom]
    rw [coprod.inl_desc, zero_comp,
      coordinate_ne X j.succ 0 (fun h => Fin.succ_ne_zero j h.symm)]
  · rw [← Category.assoc, ← Category.assoc, FiniteCoproductSuccessor.successor_hom]
    simp only [Category.assoc, coprod.inr_desc_assoc, Category.id_comp]
    by_cases h : k = j
    · subst k
      rw [coordinate_self, coordinate_self]
    · rw [coordinate_ne _ j k h, coordinate_ne X j.succ k.succ (fun e =>
      h (Fin.succ_injective n e))]

end CategoryTheory.Limits.FiniteCoproductCoordinates
