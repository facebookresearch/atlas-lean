/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GraphTheory.PartialListColoring
import Mathlib.Tactic.FinCases

@[expose] public section

namespace MathlibExt.GraphTheory.PartialListColoringWanted

example : ¬ conjecture := conjecture_refuted

/-- The explicit graph of the counterexample exists: it has 14 vertices. -/
example : Fintype.card Noel.V = 14 := by decide

/-- The explicit graph satisfies the hypothesis of `conjecture`: its choice number is `3`. -/
example : Noel.G.IsChoiceNumber 3 := noel_isChoiceNumber

/-- The explicit 2-list assignment of the paper is a genuine 2-list assignment. -/
example : Noel.IsListAssignment Noel.L 2 := by
  unfold Noel.IsListAssignment; decide

/-- The 2-list assignment is not trivially fully colorable: nine vertices can be coloured, and
the colouring is a proper list colouring in the sense of `IsListColoring`. -/
example : ∃ (S : Finset Noel.V) (f : Noel.V → ℕ),
    IsListColoring Noel.G Noel.L f S ∧ S.card = 9 := by
  refine ⟨Noel.S9, Noel.c9, ?_, by decide⟩
  have hp : Noel.IsPartialListColoring Noel.G Noel.L
      Noel.S9 Noel.c9 := by
    unfold Noel.IsPartialListColoring
    decide
  exact hp

/-- `IsChoiceNumber` is not vacuously false: the one-vertex edgeless graph has choice number one,
so `conjecture` has a nonempty class of graphs satisfying its hypothesis. -/
example : (⊥ : SimpleGraph (Fin 1)).IsChoiceNumber 1 := by
  constructor
  · intro C _ lists hlists
    obtain ⟨x, hx⟩ : ∃ x, x ∈ lists 0 :=
      Finset.card_pos.mp (by have h := hlists 0; omega)
    refine ⟨⟨fun _ => x, ?_⟩, ?_⟩
    · intro a b hab; exact absurd hab (by simp)
    · intro v; fin_cases v; exact hx
  · intro r hr h
    have hr0 : r = 0 := by omega
    subst hr0
    obtain ⟨color, hmem⟩ := h (ℕ) (fun _ => (∅ : Finset ℕ)) (by intro v; simp)
    exact absurd (hmem 0) (by simp)

end MathlibExt.GraphTheory.PartialListColoringWanted
