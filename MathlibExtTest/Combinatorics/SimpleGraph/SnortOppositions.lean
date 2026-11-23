/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Combinatorics.SimpleGraph.Hasse
import MathlibExt.Combinatorics.SimpleGraph.SnortOppositions

open MetaMathlibExt SimpleGraph

-- On the empty vertex type the identity gives the empty matching.
example (G : SimpleGraph Empty) : ∃ M : Gᶜ.Subgraph, IsOppositionMatching Gᶜ M :=
  (isOpposable_iff_exists_oppositionMatching G).mp ⟨.refl, fun v => nomatch v⟩

-- A single edge in the complement gives an opposition on two isolated vertices.
example : IsOpposable (⊥ : SimpleGraph Bool) := by
  rw [isOpposable_iff_exists_oppositionMatching, compl_bot]
  refine ⟨⊤, Subgraph.isPerfectMatching_iff.mpr ?_, ?_⟩
  · change ∀ v : Bool, ∃! w, v ≠ w
    exact fun v => ⟨!v, Bool.self_ne_not v, fun _ h => Bool.eq_not_iff.mpr h.symm⟩
  · change ∀ a b c d : Bool, a ≠ b → c ≠ d → s(a, b) ≠ s(c, d) →
      (a ≠ c ↔ b ≠ d) ∧ (a ≠ d ↔ b ≠ c)
    decide

-- The end edges of the four-vertex path are forced, but only their inner ends are adjacent.
example (M : (pathGraph 4).Subgraph) : ¬ IsOppositionMatching (pathGraph 4) M := by
  rintro ⟨hperfect, hpairs⟩
  obtain ⟨a, ha⟩ := (Subgraph.isPerfectMatching_iff.mp hperfect 0).exists
  obtain ⟨b, hb⟩ := (Subgraph.isPerfectMatching_iff.mp hperfect 3).exists
  have left : ∀ v, (pathGraph 4).Adj 0 v → v = 1 := by decide
  have right : ∀ v, (pathGraph 4).Adj 3 v → v = 2 := by decide
  obtain rfl := left a (M.adj_sub ha)
  obtain rfl := right b (M.adj_sub hb)
  have h := (hpairs 0 1 3 2 ha hb (by decide)).1
  exact (by decide : ¬ (pathGraph 4).Adj 0 3) (h.mpr (by decide))
