/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Games.Attractor
import Mathlib.Tactic.FinCases

/-!
# Tests for parity-game attractors and traps

A three-position arena on `Fin 3`: position `0` belongs to `odd`, who may stay at `0` or move to
`1`; position `1` belongs to `even` and moves to `2`; position `2` loops. The attractor of `{2}`
for `even` is `{1, 2}`: from `1` the forced move reaches `2`, while `odd` can stay at `0` forever.

* `1` lies in the second attractor stage, hence in the attractor, and the attractor strategy forces
  a visit to `{2}` from it.
* `{0}` is an `even`-trap disjoint from `{2}`, so `0` is outside the attractor, and no strategy of
  `even` forces a visit to `{2}` from `0`.
* The complement of the attractor is an `even`-trap, the attractor equals its stage at
  `Nat.card (Fin 3) = 3`, and a winning region is a trap for the opponent.
-/

@[expose] public section

namespace Cslib.Games.ParityGame.AttractorTests

/-- `0` (owned by `odd`) moves to `0` or `1`, `1` (owned by `even`) moves to `2`, `2` loops. -/
def lineGame : ParityGame (Fin 3) where
  owner v := if v = 0 then .odd else .even
  Move v w := (v = 0 ∧ (w = 0 ∨ w = 1)) ∨ (v = 1 ∧ w = 2) ∨ (v = 2 ∧ w = 2)
  priority v := v.val
  serial v := by fin_cases v <;> decide

theorem two_mem_attractor : (2 : Fin 3) ∈ lineGame.attractor .even {2} :=
  lineGame.subset_attractor .even {2} rfl

/-- `1` enters the attractor at the second stage. -/
theorem one_mem_attractorStage_two : (1 : Fin 3) ∈ lineGame.attractorStage .even {2} 2 := by
  rw [attractorStage_succ]
  refine Or.inr (Or.inl ⟨by decide, 2, Or.inr (Or.inl ⟨rfl, rfl⟩), ?_⟩)
  rw [attractorStage_succ]
  exact Or.inl rfl

theorem one_mem_attractor : (1 : Fin 3) ∈ lineGame.attractor .even {2} :=
  lineGame.attractorStage_subset_attractor .even {2} 2 one_mem_attractorStage_two

/-- From `1`, the attractor strategy forces a visit to `{2}`. -/
example : lineGame.ForcesReach (lineGame.attractorStrategy .even {2}) {2} 1 :=
  forcesReach_attractorStrategy one_mem_attractor

/-- `{0}` is an `even`-trap: `odd` owns `0` and can stay there. -/
theorem isTrap_zero : lineGame.IsTrap .even {0} := by
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  subst hv
  exact ⟨fun h => absurd h (by decide), fun _ => ⟨0, Or.inl ⟨rfl, Or.inl rfl⟩, rfl⟩⟩

theorem zero_notMem_attractor : (0 : Fin 3) ∉ lineGame.attractor .even {2} := fun h =>
  Set.disjoint_left.mp (isTrap_zero.disjoint_attractor (by simp)) rfl h

/-- `even` has no positional strategy forcing a visit to `{2}` from `0`. -/
example : ¬ ∃ σ : lineGame.PositionalStrategy .even, lineGame.ForcesReach σ {2} 0 := fun h =>
  zero_notMem_attractor (mem_attractor_iff.mpr h)

/-- The attractor of `{2}` for `even` is `{1, 2}`. -/
example : lineGame.attractor .even {2} = {1, 2} := by
  ext v
  fin_cases v
  · simpa using zero_notMem_attractor
  · simpa using one_mem_attractor
  · simpa using two_mem_attractor

/-- The complement of the attractor is an `even`-trap. -/
example : lineGame.IsTrap .even (lineGame.attractor .even {2})ᶜ :=
  isTrap_compl_attractor lineGame .even {2}

/-- On this arena the attractor is its stage at `Nat.card (Fin 3) = 3`. -/
example : lineGame.attractor .even {2} = lineGame.attractorStage .even {2} 3 := by
  simpa using attractor_eq_attractorStage_card lineGame .even {2}

/-- The winning region of `even` is a trap for `odd`. -/
example : lineGame.IsTrap .odd (lineGame.WinningRegion .even) :=
  isTrap_winningRegion lineGame .even

end Cslib.Games.ParityGame.AttractorTests
