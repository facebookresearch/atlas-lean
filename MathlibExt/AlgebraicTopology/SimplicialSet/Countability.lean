/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
public import Mathlib.Basic.Countable.Basic

/-!
# Countability of simplicial sets

Countably many nondegenerate simplices imply countability of every degree
and of the total set of simplices. The degree theorem is reused unchanged
from its original general formulation, now in a neutral module.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-- If a simplicial set has countably many non-degenerate simplices, then
every one of its simplex types is countable: an `n`-simplex is the image
of a non-degenerate `m`-simplex (`m ≤ n`) under one of finitely many maps
`⦋n⦌ ⟶ ⦋m⦌`. This is the counting input that allows an arbitrary
two-vertex `B` satisfying Stevenson's conditions to be recoded as a
`SSet.NatModel`. -/
theorem countable_obj_of_countable_N (B : SSet.{u}) [Countable B.N]
    (x : SimplexCategoryᵒᵖ) : Countable (B.obj x) := by
  obtain ⟨s⟩ := x
  induction s using SimplexCategory.rec with
  | _ n =>
    have hnd : ∀ m : ℕ, Countable (B.nonDegenerate m) := fun m ↦
      Function.Injective.countable (f := fun x ↦ N.mk _ x.property)
        (fun x y h ↦ by
          rw [N.ext_iff, S.ext_iff'] at h
          aesop)
    let φ : (Σ (m : Fin (n + 1)) (f : ⦋n⦌ ⟶ ⦋m.1⦌),
        B.nonDegenerate m.1) → B _⦋n⦌ :=
      fun ⟨m, f, y⟩ ↦ B.map f.op y.1
    exact Function.Surjective.countable (f := φ) (fun a ↦ by
      obtain ⟨m, f, hf, y, rfl⟩ := B.exists_nonDegenerate a
      have := SimplexCategory.le_of_epi f
      exact ⟨⟨⟨m, by lia⟩, f, y⟩, rfl⟩)

/-- All degrees together are countable when the nondegenerate simplices are countable. -/
theorem countable_sigma_obj_of_countable_N (X : SSet.{u}) [Countable X.N] :
    Countable (Σ n : ℕ, X _⦋n⦌) := by
  have : ∀ n : ℕ, Countable (X _⦋n⦌) := fun n =>
    countable_obj_of_countable_N X (op ⦋n⦌)
  infer_instance

end SSet
