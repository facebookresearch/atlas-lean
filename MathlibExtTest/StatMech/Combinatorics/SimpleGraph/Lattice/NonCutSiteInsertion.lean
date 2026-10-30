/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.NonCutSiteInsertion
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.NonCutSiteInsertion`

* `tnbp_reachable_of_avoid` on the complete graph on `Fin 4` with vertex `0` removed.
* `tnbp_RingClear` holds for the origin and the far site `{(5, 5)}`, so by
  `tnbp_neighbours_connected_of_ringClear` the origin is a non-cut site for it.
* A two-site ring chain `[(0, 0), (5, 5)]` (a nontrivial instance of `tnbp_RingChain`, beyond the
  singleton case), and `tnbp_reachesExterior_ringChain` for it: the complement of the two sites
  is connected (via `arcxc_connected_of_reachesExterior`).
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.NonCutSiteInsertion

/-- The complete graph on `Fin 4` with the edges at `0` removed. -/
def G' : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun a b => a ≠ 0 ∧ b ≠ 0

example : G'.Reachable 1 2 :=
  tnbp_reachable_of_avoid ⊤ G' 0
    (fun a b => by simp only [G', fromRel_adj, top_adj]; tauto)
    (fun p q hp hq => by
      by_cases h : p = q
      · exact h ▸ Reachable.refl p
      · exact Adj.reachable (by simp only [G', fromRel_adj]; exact ⟨h, Or.inl ⟨hp.ne', hq.ne'⟩⟩))
    (by decide) (by decide) ((top_adj 1 2).2 (by decide)).reachable

theorem ringClear_origin : tnbp_RingClear ![0, 0] {![5, 5]} := by
  simp [tnbp_RingClear]

example : tnbp_RingConnected ![0, 0] {![5, 5]} :=
  tnbp_neighbours_connected_of_ringClear ringClear_origin

theorem ringChain_two : tnbp_RingChain [![0, 0], ![5, 5]] := by
  refine ⟨?_, tnbp_ringChain_singleton _⟩
  have : {x : Site 2 | x ∈ [![5, 5]]} = {![5, 5]} := by ext; simp
  rw [this]
  exact tnbp_neighbours_connected_of_ringClear ringClear_origin

theorem twoSites_box : ∀ c ∈ [(![0, 0] : Site 2), ![5, 5]], c ∈ box 2 5 := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> (rw [mem_box]; intro i; fin_cases i <;> simp)

example : arcxc_ReachesExterior {x : Site 2 | x ∈ [![0, 0], ![5, 5]]} 5 :=
  tnbp_reachesExterior_ringChain twoSites_box ringChain_two

example : arcns_OffSupportConnected {x : Site 2 | x ∈ [![0, 0], ![5, 5]]} :=
  arcxc_connected_of_reachesExterior (tnbp_reachesExterior_ringChain twoSites_box ringChain_two)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.NonCutSiteInsertion
