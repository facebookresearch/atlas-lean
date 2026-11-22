/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.PartialListColoring

@[expose] public section

namespace MathlibExt.GraphTheory.PartialListColoringWanted

example : ¬ conjecture := conjecture_refuted

/-- Noel's graph has fourteen vertices. -/
example : Fintype.card Noel.V = 14 := by decide

/-- Noel's graph is the paper's: each `{u i, v i, p i}` is a triangle, the terminals are adjacent
exactly to the non-private vertices `u i` and `v i`, and there are no other edges. -/
example : ∀ a b : Noel.V, Noel.G.Adj a b ↔
    (∃ i, (a = .u i ∨ a = .v i ∨ a = .p i) ∧ (b = .u i ∨ b = .v i ∨ b = .p i) ∧ a ≠ b) ∨
    ((a = .s1 ∨ a = .s2) ∧ ∃ i, b = .u i ∨ b = .v i) ∨
    ((b = .s1 ∨ b = .s2) ∧ ∃ i, a = .u i ∨ a = .v i) := by
  decide

/-- Noel's graph satisfies the hypothesis of `conjecture` with `χ_ℓ = 3`. -/
example : Noel.G.IsChoiceNumber 3 := Noel.isChoiceNumber_three

/-- Noel's lists all have two colours. -/
example : ∀ w : Noel.V, (Noel.L w).card = 2 := by decide

/-- Each choice of one colour from each terminal's list is the list of a triangle, and the four
triangles have distinct lists. -/
example : (∀ a ∈ Noel.L .s1, ∀ b ∈ Noel.L .s2, ∃ i, Noel.listOf i = {a, b}) ∧
    Function.Injective Noel.listOf := by
  decide

/-- Nine vertices can be coloured from Noel's lists, so `λ_L = 9`: the bound is attained. -/
example : lambdaMax Noel.G Noel.L = 9 := by
  let S : Finset Noel.V := {.s1, .s2, .p 0, .u 1, .p 1, .u 2, .p 2, .u 3, .v 3}
  let c : Noel.V → ℕ
    | .s1 => 0
    | .s2 => 2
    | .p 0 => 0
    | .u 1 => 3
    | .p 1 => 0
    | .u 2 => 1
    | .p 2 => 2
    | .u 3 => 1
    | .v 3 => 3
    | _ => 0
  have hS : IsListColoring Noel.G Noel.L c S := by
    unfold IsListColoring
    decide
  have h9 : S.card = 9 := by decide
  exact le_antisymm Noel.lambdaMax_L_le_nine (h9 ▸ card_le_lambdaMax hS)

/-- `λ_2 ≤ 9 < 14 = λ_3` for Noel's graph. -/
example : lambdaMin Noel.G 2 ≤ 9 ∧ lambdaMin Noel.G 3 = 14 :=
  ⟨Noel.lambdaMin_two_le_nine, Noel.lambdaMin_three⟩

/-- On a graph without edges, nonempty lists colour every vertex. -/
example : lambdaMin (⊥ : SimpleGraph (Fin 3)) 1 = 3 := by
  apply le_antisymm
  · calc lambdaMin (⊥ : SimpleGraph (Fin 3)) 1 ≤ lambdaMax ⊥ (fun _ => {0}) :=
          lambdaMin_le_lambdaMax fun _ => by simp
      _ ≤ 3 := (lambdaMax_le_card _ _).trans (by simp)
  · refine le_lambdaMin fun L hL => ?_
    have hne : ∀ v, (L v).Nonempty := fun v => Finset.card_pos.mp (by simp [hL v])
    have h := card_le_lambdaMax (G := (⊥ : SimpleGraph (Fin 3))) (L := L) (S := Finset.univ)
      (f := fun v => (hne v).choose) ⟨fun v _ => (hne v).choose_spec, by simp⟩
    simpa using h

/-- Empty lists colour no vertex. -/
example : lambdaMin (⊤ : SimpleGraph (Fin 2)) 0 = 0 := by
  refine Nat.le_zero.mp ((lambdaMin_le_lambdaMax (L := fun _ => ∅) fun _ => by simp).trans ?_)
  refine lambdaMax_le fun S f h => ?_
  rw [Nat.le_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro v hv
  simpa using h.1 v hv

end MathlibExt.GraphTheory.PartialListColoringWanted
