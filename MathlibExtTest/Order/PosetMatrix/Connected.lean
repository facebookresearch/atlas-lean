/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Order.PosetMatrix.Connected
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Sum.Order

/-!
# Tests for connectedness of posets represented by block matrices
-/

namespace MetaMathlibExt

-- The unique cut in a two-element chain has a block of ones.
example (S : Set (Fin 2)) (hS : ∀ x y : Fin 2, x ≤ y → (x ∈ S ↔ y ∈ S)) :
    S = ∅ ∨ S = Set.univ := by
  let M : Matrix (Fin 2) (Fin 2) Bool := fun i j => decide (i ≤ j)
  have hM : IsPosetMatrix 2 M := by unfold IsPosetMatrix M; decide
  exact (connected_or_disconnected_of_block_property 2 M hM (Equiv.refl (Fin 2))
    (by simp [M]) 1 (by decide) (by decide)).1 (by decide) S hS

-- The same cut in the identity matrix separates two incomparable singletons.
example : ∃ S : Set (Fin 1 ⊕ Fin 1), S.Nonempty ∧ Sᶜ.Nonempty ∧
    ∀ x y : Fin 1 ⊕ Fin 1, x ≤ y → (x ∈ S ↔ y ∈ S) := by
  let M : Matrix (Fin 2) (Fin 2) Bool := fun i j => decide (i = j)
  have hM : IsPosetMatrix 2 M := by unfold IsPosetMatrix M; decide
  let e := (finSumFinEquiv (m := 1) (n := 1)).symm
  have he (i j : Fin 2) : e i ≤ e j ↔ M i j = true := by
    change e i ≤ e j ↔ decide (i = j) = true
    rw [decide_eq_true_eq, ← e.injective.eq_iff]
    cases e i <;> cases e j <;> simp [Fin.fin_one_eq_zero]
  exact (connected_or_disconnected_of_block_property 2 M hM e he 1
    (by decide) (by decide)).2 (by decide)

end MetaMathlibExt
