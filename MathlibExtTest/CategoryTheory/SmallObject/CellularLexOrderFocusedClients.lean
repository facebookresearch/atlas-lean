/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.LexicographicOrder
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Order.SuccPred.Fin
import Mathlib.Order.SuccPred.Nat

/-!
# Focused clients for dependent lexicographic cellular orders

* `Σ _ : ℕ, ℕ` with the lexicographic order is well founded although `⟨1, 0⟩`
  has infinitely many predecessors.
* In `Σ j : ℕ, Fin (j + 2)`, an inner successor and the jump from a greatest inner
  vertex to the next outer bottom are covers.
* In `Σ _ : Fin 2, Fin 3`, a vertex is maximal exactly when both coordinates are;
  an inner maximum below a non-maximal outer vertex is not maximal.
* A flattened vertex with a non-limit nonbottom inner coordinate is not a limit.
-/

open CategoryTheory.SmallObject.CellularNormalization

namespace MathlibExtTest.CategoryTheory.SmallObject.CellularLexOrder

/-- The lexicographic order on `Σ _ : ℕ, ℕ` (order type `ω²`) is well founded. -/
instance wellFoundedLT_lex : WellFoundedLT (Lex (Σ _ : ℕ, ℕ)) :=
  lexWellFounded (J := ℕ) (K := fun _ => ℕ)

/-- The vertex `⟨1, 0⟩` lies above every vertex of the first outer block. -/
lemma lt_one_zero (n : ℕ) :
    (toLex ⟨0, n⟩ : Lex (Σ _ : ℕ, ℕ)) < toLex ⟨1, 0⟩ :=
  Sigma.Lex.left _ _ Nat.zero_lt_one

/-- Well-foundedness despite infinitely many predecessors of `⟨1, 0⟩`: every
nonempty set of vertices, here the infinite first block, has a minimal element. -/
example : ∃ a ∈ {b : Lex (Σ _ : ℕ, ℕ) | b < toLex ⟨1, 0⟩},
    ∀ b ∈ {b : Lex (Σ _ : ℕ, ℕ) | b < toLex ⟨1, 0⟩}, ¬ b < a :=
  WellFounded.has_min wellFounded_lt _ ⟨_, lt_one_zero 0⟩

/-- The first block below `⟨1, 0⟩` is infinite. -/
example : Set.Infinite {b : Lex (Σ _ : ℕ, ℕ) | b < toLex ⟨1, 0⟩} :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (toLex ⟨0, n⟩ : Lex (Σ _ : ℕ, ℕ)))
    (fun m n h => by simpa using h) lt_one_zero

/-- An inner successor is a cover of the flattened order. -/
example : (toLex ⟨2, 0⟩ : Lex (Σ j : ℕ, Fin (j + 2))) ⋖ toLex ⟨2, Order.succ 0⟩ :=
  inner_covBy (K := fun j : ℕ => Fin (j + 2)) (not_isMax_iff.2 ⟨1, by decide⟩)

/-- The greatest inner vertex of block `0` is covered by the bottom of block `1`. -/
example : (toLex ⟨0, Fin.last 1⟩ : Lex (Σ j : ℕ, Fin (j + 2))) ⋖ toLex ⟨1, ⊥⟩ := by
  have h := join_covBy (K := fun j : ℕ => Fin (j + 2)) (not_isMax (0 : ℕ))
    (k := Fin.last 1) (fun l _ => Fin.le_last l)
  rwa [Order.succ_eq_add_one, zero_add] at h

/-- Both coordinates maximal: the flattened vertex is maximal. -/
example : IsMax (toLex ⟨1, 2⟩ : Lex (Σ _ : Fin 2, Fin 3)) :=
  (flat_isMax_iff (K := fun _ : Fin 2 => Fin 3) 1 2).2
    ⟨fun j _ => Fin.le_last j, fun l _ => Fin.le_last l⟩

/-- A greatest inner vertex below a non-maximal outer vertex is not maximal. -/
example : ¬ IsMax (toLex ⟨0, 2⟩ : Lex (Σ _ : Fin 2, Fin 3)) := by
  rw [flat_isMax_iff (K := fun _ : Fin 2 => Fin 3)]
  rintro ⟨h, -⟩
  exact absurd (h (show (0 : Fin 2) ≤ 1 by decide)) (by decide)

/-- A flattened vertex whose inner coordinate is the nonbottom successor `1`
is not a successor limit. -/
example : ¬ Order.IsSuccLimit (toLex ⟨3, 1⟩ : Lex (Σ j : ℕ, Fin (j + 2))) := by
  intro h
  have hl := inner_limit_of_flat_limit (K := fun j : ℕ => Fin (j + 2)) h (by decide)
  have h1 : (1 : Fin 5) = Order.succ 0 := by decide
  rw [h1] at hl
  exact hl.isSuccPrelimit _ (Order.covBy_succ_of_not_isMax (not_isMax_iff.2 ⟨1, by decide⟩))

end MathlibExtTest.CategoryTheory.SmallObject.CellularLexOrder
