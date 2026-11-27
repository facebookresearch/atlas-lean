/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.Matching.HousingMarket

/-! # Tests for original-house blocking and the Shapley–Scarf cores -/

namespace MathlibExtTest.GameTheory.Matching.HousingMarket

open MathlibExt.GameTheory.Matching
open HousingMarket

-- Check each adjacent comparison, not just the top choices or the separating allocation.
example : (threeAgentMarket.pref 0).lt 1 0 ∧ (threeAgentMarket.pref 0).lt 0 2 ∧
    (threeAgentMarket.pref 1).lt 0 2 ∧ (threeAgentMarket.pref 1).lt 2 1 ∧
    (threeAgentMarket.pref 2).lt 0 1 ∧ (threeAgentMarket.pref 2).lt 1 2 := by decide

example : (∀ i, threeAgentMarket.endowment i = i) ∧
    finRotate 3 0 = 1 ∧ finRotate 3 1 = 2 ∧ finRotate 3 2 = 0 := by decide

-- With just one house, every feasible offer equals the current house. Equality for everyone
-- is not a weak block: both cores contain the unique allocation, for any strict preference.
example (M : HousingMarket (Fin 1) (Fin 1)) (x : Fin 1 ≃ Fin 1) :
    x ∈ M.strictCore ∧ x ∈ M.weakCore := by
  have hs : x ∈ M.strictCore := by
    rintro S ⟨_, σ, _, i, hi⟩
    exact (M.pref i).irrefl (x i) (Subsingleton.elim (M.endowment (σ i)) (x i) ▸ hi)
  exact ⟨hs, M.strictCore_subset_weakCore hs⟩

-- A singleton can strictly improve on the rotation when (and because) its endowment changes.
-- Giving agent 1 original house 0, rather than original house 1, makes reclaiming it profitable.
example : ¬ threeAgentMarket.StrictlyBlocks (finRotate 3) {1} := by
  rw [strictlyBlocks_singleton_iff]
  decide

example : ({ threeAgentMarket with endowment := Equiv.swap 0 1 }).StrictlyBlocks
    (finRotate 3) {1} := by
  rw [strictlyBlocks_singleton_iff]
  decide

-- The pair's weak block disappears if it must trade the *assigned* houses 1 and 2 instead:
-- neither member could get house 0, the only improvement for agent 1, and agent 0 is at the top.
example : ¬ ({ threeAgentMarket with endowment := finRotate 3 }).WeaklyBlocks
    (finRotate 3) {0, 1} := by
  rintro ⟨_, σ, _, i, hi⟩
  have no_gain : ∀ a b : Fin 3, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
      ¬ (threeAgentMarket.pref a).lt (finRotate 3 b) (finRotate 3 a) := by decide
  have member (j : ({0, 1} : Finset (Fin 3))) : (j : Fin 3) = 0 ∨ (j : Fin 3) = 1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using j.property
  exact no_gain i (σ i) (member i) (member (σ i)) hi

-- Nonemptiness matters even for all-strict blocking (the universal comparison alone is vacuous).
example {A H : Type*} [Finite A] [Nonempty A] (M : HousingMarket A H) (x : A ≃ H) :
    ¬ M.StrictlyBlocks x ∅ := fun h => Finset.not_nonempty_empty h.1

end MathlibExtTest.GameTheory.Matching.HousingMarket
