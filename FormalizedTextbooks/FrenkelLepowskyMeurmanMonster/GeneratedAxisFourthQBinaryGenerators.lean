/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions
public import Mathlib.LinearAlgebra.Pi

/-! Coordinate generators of a binary additive group, used through actual group equivalences. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A subgroup containing every binary coordinate generator contains the entire binary group. -/
theorem generatedFourthQBinaryBasis_generates (n : ℕ)
    (H : Subgroup (Multiplicative (Fin n → ZMod 2)))
    (hH : ∀ i : Fin n, Multiplicative.ofAdd (Pi.single i 1) ∈ H) : H = ⊤ := by
  classical
  apply top_unique
  intro w _
  have hc (i : Fin n) :
      Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd w i)) ∈ H := by
    have hh (c : ZMod 2) : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hh (Multiplicative.toAdd w i) with hz | ho
    · rw [hz, Pi.single_zero]
      exact H.one_mem
    · rw [ho]
      exact hH i
  have hp : (∏ i : Fin n,
      Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd w i))) ∈ H :=
    H.prod_mem (fun i _ => hc i)
  rw [← ofAdd_sum, LinearMap.sum_single_apply] at hp
  exact hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
