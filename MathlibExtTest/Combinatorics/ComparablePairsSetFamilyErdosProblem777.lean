/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ComparablePairsSetFamilyErdosProblem777

open MathlibExt.Combinatorics.ComparablePairsSetFamilyErdosProblem777Wanted

-- The middle layer on two points is an antichain.
example : comparablePairs ({{0}, {1}} : Finset (Finset (Fin 2))) = 0 := by
  unfold comparablePairs
  decide

-- In the full square there are four cover relations and one further strict containment.
private theorem square_pairs : comparablePairs (Finset.univ : Finset (Finset (Fin 2))) = 5 := by
  unfold comparablePairs
  decide

-- For ε = 1 the full square has size 4, above the cutoff 3, so its five pairs must
-- be at or below the density threshold for the δ supplied by the theorem.
example : ∃ δ : ℝ, 0 < δ ∧ 5 ≤ (4 : ℝ) ^ (2 - δ) := by
  obtain ⟨δ, hδ, h⟩ := nearlyCompleteComparabilityFamilySmall_holds 1 zero_lt_one
  refine ⟨δ, hδ, ?_⟩
  specialize h 2 (Finset.univ : Finset (Finset (Fin 2)))
  norm_num [square_pairs] at h
  exact h

-- At n = 4 the two stacked squares satisfy the size bound for ε = 1/4 with equality,
-- yet have more than 2^4 comparable pairs. The eventual quantifier matters.
private def stackedSquares : Finset (Finset (Fin 4)) :=
  Finset.univ.filter fun s ↦ s ⊆ {0, 1} ∨ {0, 1} ⊆ s

example : stackedSquares.card = 7 ∧ comparablePairs stackedSquares = 19 := by
  unfold comparablePairs stackedSquares
  decide

example : ∀ᶠ n : ℕ in Filter.atTop, ∀ F : Finset (Finset (Fin n)),
    (F.card : ℝ) ≤ (7 / 4) * 2 ^ ((n : ℝ) / 2) → comparablePairs F < 2 ^ n := by
  convert fewComparablePairsBelowTwoHalfPower_holds (1 / 4) (by norm_num) using 1
  norm_num
