/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/WrittenOnTheWallII/GraphConjecture314.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.WellTotallyDominatedP5Free

@[expose] public section

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.WellTotallyDominatedP5Free`
-/

open SimpleGraph WrittenOnTheWallII.GraphConjecture314

namespace MathlibExtTest.Combinatorics.SimpleGraphTests.WellTotallyDominatedP5Free

-- Source faithfulness: the Formal Conjectures statement
-- `WrittenOnTheWallII.GraphConjecture314.conjecture314`, verbatim.
example {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4) :
    IsWellTotallyDominated G :=
  conjecture314 G hG hTriFree hPath

-- Sanity checks carried by the Formal Conjectures file.
example : ∃ a b c : Fin 3, (⊤ : SimpleGraph (Fin 3)).Adj a b ∧
    (⊤ : SimpleGraph (Fin 3)).Adj b c ∧ (⊤ : SimpleGraph (Fin 3)).Adj c a :=
  ⟨0, 1, 2, by decide, by decide, by decide⟩

example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] :
    0 ≤ largestInducedPathSize G := Nat.zero_le _

-- Total domination is strictly stronger than ordinary domination: in `K₂` the set `{0}`
-- dominates every vertex outside it, but is not a total dominating set, because `0` has
-- no neighbour in it.
example : ¬ IsTotalDominatingSet (⊤ : SimpleGraph (Fin 2)) {0} := by
  intro h
  obtain ⟨w, hw, hadj⟩ := h 0
  rw [Finset.mem_singleton] at hw
  subst hw
  exact (⊤ : SimpleGraph (Fin 2)).irrefl hadj

-- Both vertices of `K₂` do form a total dominating set.
example : IsTotalDominatingSet (⊤ : SimpleGraph (Fin 2)) {0, 1} := by
  intro v
  fin_cases v
  · exact ⟨1, by simp, by decide⟩
  · exact ⟨0, by simp, by decide⟩

end MathlibExtTest.Combinatorics.SimpleGraphTests.WellTotallyDominatedP5Free
