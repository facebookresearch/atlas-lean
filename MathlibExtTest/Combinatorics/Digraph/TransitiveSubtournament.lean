/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Digraph.TransitiveSubtournament

namespace MathlibExtTest.Combinatorics.Digraph.TransitiveSubtournament

open MathlibExt.Combinatorics.TransitiveSubtournamentLogErdosProblem1216Wanted

private def cycle (x y : Fin 3) : Prop := y = x + 1

private theorem cycle_tournament : IsTournament cycle := by
  unfold IsTournament cycle
  decide

private theorem cycle_not_transitive : ¬ IsTransitiveOn cycle Finset.univ := by
  unfold IsTransitiveOn cycle
  decide

-- A pair is always transitive, while the directed triangle prevents a guarantee of three.
example : transitiveSubtournamentNumber 3 = 2 := by
  let sizes := {m : ℕ | ∀ T : Fin 3 → Fin 3 → Prop, IsTournament T →
    ∃ s : Finset (Fin 3), s.card = m ∧ IsTransitiveOn T s}
  have upper : ∀ m ∈ sizes, m ≤ 2 := by
    intro m hm
    obtain ⟨s, rfl, htr⟩ := hm cycle cycle_tournament
    have hs : s ≠ Finset.univ := fun e => cycle_not_transitive (e ▸ htr)
    have h := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hs)
    simpa using Nat.le_of_lt_succ h
  have pair : 2 ∈ sizes := by
    intro T ht
    refine ⟨{0, 1}, by decide, ?_⟩
    intro x hx y hy z hz hxy hyz
    have hxx := ht.1
    have hanti := (ht.2 0 1 (by decide)).mp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
      solve_by_elim
  exact le_antisymm (csSup_le ⟨2, pair⟩ upper) (le_csSup ⟨2, upper⟩ pair)

end MathlibExtTest.Combinatorics.Digraph.TransitiveSubtournament
