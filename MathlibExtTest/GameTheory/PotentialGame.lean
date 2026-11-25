/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.PotentialGame

open MathlibExt.GameTheory.PotentialGame

/-- An identical-interest game, where every player's cost is the same function `Φ`, has
`Φ` as an exact potential. -/
example {ι : Type*} [DecidableEq ι] {S : ι → Type*} (Φ : (∀ i, S i) → ℝ) :
    IsExactPotential (fun _ => Φ) Φ := fun _ _ _ => rfl

/-- Two players each pick one of two links, and a link used by `n` players has delay `n`. -/
noncomputable def twoLinks : CongestionGame (Fin 2) (Fin 2) (fun _ => Fin 2) where
  uses _ a := {a}
  delay _ n := n

/-- When both players pick link `0`, its load is `2`. -/
example : twoLinks.load (fun _ => 0) 0 = 2 := by decide

/-- The two-link congestion game has a pure Nash equilibrium (Rosenthal). -/
example : ∃ s, IsPureNash twoLinks.cost s := twoLinks.exists_isPureNash

/-- Both players on link `0` is not an equilibrium: player `0` gains by moving to link `1`. -/
example : ¬ IsPureNash twoLinks.cost (fun _ => 0) := by
  intro h
  have := h 0 1
  simp [CongestionGame.cost, CongestionGame.load, twoLinks] at this
  norm_num [Finset.filter_singleton, Function.update_apply] at this
  revert this
  decide

/-- Improvement paths in the two-link game are finite. -/
example : WellFounded (ImprovingMove twoLinks.cost) :=
  twoLinks.isExactPotential_potential.wellFounded_improvingMove

/-- The harmonic factor for two players is `3/2`. -/
example : (harmonic 2 : ℝ) = 3 / 2 := by norm_num [harmonic, Finset.sum_range_succ]

/-- Price of stability in a two-player fair cost-sharing game: some equilibrium costs at
most `3/2` times every profile. -/
example {S : Fin 2 → Type*} [∀ i, Finite (S i)] [∀ i, Nonempty (S i)] {R : Type*}
    [Fintype R] [DecidableEq R] (G : FairCostSharing (Fin 2) R S) :
    ∃ s, IsPureNash G.toCongestionGame.cost s ∧
      ∀ t, G.networkCost s ≤ 3 / 2 * G.networkCost t := by
  obtain ⟨s, hs, h⟩ := G.exists_isPureNash_networkCost_le
  refine ⟨s, hs, fun t => ?_⟩
  have := h t
  norm_num [harmonic, Finset.sum_range_succ] at this
  linarith

#print axioms CongestionGame.isExactPotential_potential
#print axioms FairCostSharing.exists_isPureNash_networkCost_le
#print axioms IsExactPotential.wellFounded_improvingMove
