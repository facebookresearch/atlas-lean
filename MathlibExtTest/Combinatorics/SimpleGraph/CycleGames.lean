/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.CycleGames

/-!
# Cycle-closing regression tests on `K₃`

The `K₂` facts in
`MathlibExt.Combinatorics.SimpleGraph.CycleGames` only exercise dead-end
positions, where Make-A-Cycle and Avoid-A-Cycle behave identically. On `K₃`
the two games differ from the same start: Make-A-Cycle wins by completing the
cycle (revisiting a non-previous vertex), while Avoid-A-Cycle loses because
every continuation revisits a vertex. These tests pin the defining
visited-vertex branch of both recurrences.
-/

@[expose] public section

namespace MetaMathlibExt

namespace CycleGamesTests

/-- On `K₃`, Player 1 wins Make-A-Cycle from the start: move `0 → 1 → 2`,
then revisit `0`, which is visited and is not the previous vertex. -/
theorem makeACycleWins_top_fin_three :
    makeACycleWins (⊤ : SimpleGraph (Fin 3)) {0} none 0 := by
  have hfull : makeACycleWins (⊤ : SimpleGraph (Fin 3))
      (insert 2 (insert 1 {0})) (some 1) 2 := by
    rw [makeACycleWins_iff]
    exact ⟨0, by simp, by simp, Or.inl (by simp)⟩
  rw [makeACycleWins_iff]
  refine ⟨1, by simp, by simp, Or.inr ⟨by simp, ?_⟩⟩
  rw [makeACycleWins_iff]
  rintro ⟨w, hw, hp, h⟩
  fin_cases w
  · simp at hp
  · simp at hw
  · rcases h with h | ⟨-, hneg⟩
    · simp at h
    · exact hneg hfull

/-- From a position where every vertex is visited, Avoid-A-Cycle is lost:
every candidate move revisits a vertex. -/
theorem not_avoidACycleWins_of_all_mem {S : Finset (Fin 3)} (hS : ∀ w, w ∈ S)
    {p : Option (Fin 3)} {c : Fin 3} :
    ¬ avoidACycleWins (⊤ : SimpleGraph (Fin 3)) S p c := by
  rw [avoidACycleWins_iff]
  rintro ⟨w, -, -, hnot, -⟩
  exact hnot (hS w)

/-- On `K₃`, Player 1 loses Avoid-A-Cycle from the start: every first move
leaves two visited vertices, and the only continuation revisits one. -/
theorem not_avoidACycleWins_top_fin_three :
    ¬ avoidACycleWins (⊤ : SimpleGraph (Fin 3)) {0} none 0 := by
  rw [avoidACycleWins_iff]
  rintro ⟨w, -, -, hnot, hneg⟩
  fin_cases w
  · simp at hnot
  · apply hneg
    rw [avoidACycleWins_iff]
    refine ⟨2, by simp, by simp, by simp, ?_⟩
    exact not_avoidACycleWins_of_all_mem (fun w => by fin_cases w <;> simp)
  · apply hneg
    rw [avoidACycleWins_iff]
    refine ⟨1, by simp, by simp, by simp, ?_⟩
    exact not_avoidACycleWins_of_all_mem (fun w => by fin_cases w <;> simp)

#print axioms makeACycleWins_top_fin_three
#print axioms not_avoidACycleWins_top_fin_three

end CycleGamesTests

end MetaMathlibExt
