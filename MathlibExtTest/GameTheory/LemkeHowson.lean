/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.LemkeHowson
import Mathlib.Order.Interval.Set.Infinite

/-! # Tests for `MathlibExt.GameTheory.LemkeHowson`

Pure strategies give matrix entries as expected payoffs. In a `1 × 2` game where player 2
strictly prefers the second column, the best responses are computed, the game is nondegenerate,
the pure profile `(0, 1)` is an equilibrium and `(0, 0)` is not, and the theorem applies. The
all-zero `2 × 2` game is degenerate and every profile is an equilibrium, so its set of
equilibria is infinite and `ncard` is `0`: the conclusion fails without nondegeneracy. -/

namespace MathlibExtTest.GameTheory.LemkeHowson

open Convexity MathlibExt.GameTheory.LemkeHowsonWanted

-- Test section: expected payoffs. Pure strategies give the matrix entry.
example (C : Fin 2 → Fin 3 → ℝ) (i : Fin 2) (j : Fin 3) :
    bilinPayoff C (StdSimplex.single i) (StdSimplex.single j) = C i j := by
  simp [bilinPayoff, Finsupp.single_apply]

-- Test section: a nondegenerate `1 × 2` game. Player 1 has one strategy; player 2 gets `0` from
-- column `0` and `1` from column `1`.

/-- Player 1's payoffs in the `1 × 2` test game. -/
def lhTestA : Fin 1 → Fin 2 → ℝ := fun _ _ => 0

/-- Player 2's payoffs in the `1 × 2` test game. -/
def lhTestB : Fin 1 → Fin 2 → ℝ := fun _ j => if j = 0 then 0 else 1

theorem lhTest_bestResponses₂ (x : StdSimplex ℝ (Fin 1)) : bestResponses₂ lhTestB x = {1} := by
  ext j
  simp only [bestResponses₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Fin.sum_univ_one, StdSimplex.weights_apply_eq_one, one_mul, lhTestB, Fin.forall_fin_two]
  fin_cases j <;> norm_num

example (y : StdSimplex ℝ (Fin 2)) : bestResponses₁ lhTestA y = Finset.univ := by
  ext i
  simp [bestResponses₁, lhTestA]

theorem lhTest_isNondegenerate : IsNondegenerate lhTestA lhTestB := by
  refine ⟨fun x => ?_, fun y => ?_⟩
  · rw [lhTest_bestResponses₂, Finset.card_singleton]
    exact Finset.card_pos.2 x.support_weights_nonempty
  · calc (bestResponses₁ lhTestA y).card ≤ Fintype.card (Fin 1) := Finset.card_le_univ _
      _ = 1 := Fintype.card_fin 1
      _ ≤ y.weights.support.card := Finset.card_pos.2 y.support_weights_nonempty

-- Player 2 playing column `1` against the only strategy of player 1 is an equilibrium.
example : IsBimatrixNash lhTestA lhTestB (StdSimplex.single 0) (StdSimplex.single 1) := by
  refine ⟨fun x' => by simp [bilinPayoff, lhTestA], fun y' => ?_⟩
  simp [bilinPayoff, lhTestB, Fin.sum_univ_two, Finsupp.single_apply]

-- Column `0` is not: player 2 gains by switching to column `1`.
example : ¬ IsBimatrixNash lhTestA lhTestB (StdSimplex.single 0) (StdSimplex.single 0) := by
  intro h
  have := h.2 (StdSimplex.single 1)
  norm_num [bilinPayoff, lhTestB, Finsupp.single_apply] at this

-- The theorem applies: the game has an odd number of equilibria.
example :
    Odd {p : StdSimplex ℝ (Fin 1) × StdSimplex ℝ (Fin 2) |
      IsBimatrixNash lhTestA lhTestB p.1 p.2}.ncard :=
  odd_ncard_isBimatrixNash lhTestA lhTestB lhTest_isNondegenerate

-- Test section: the all-zero `2 × 2` game. It is degenerate: against a pure strategy of player 1,
-- both columns are best responses.
example : ¬ IsNondegenerate (fun _ _ => 0 : Fin 2 → Fin 2 → ℝ) (fun _ _ => 0) := by
  rintro ⟨h, -⟩
  have hBR : bestResponses₂ (fun _ _ => 0 : Fin 2 → Fin 2 → ℝ) (StdSimplex.single 0) =
      Finset.univ := by
    ext j
    simp [bestResponses₂]
  have := h (StdSimplex.single 0)
  rw [hBR, StdSimplex.weights_single, Finsupp.support_single _ one_ne_zero] at this
  simp at this

-- Every profile of the zero game is an equilibrium, so the set of equilibria is infinite, its
-- `ncard` is `0`, and the conclusion of the theorem fails: nondegeneracy cannot be dropped.
example :
    ¬ Odd {p : StdSimplex ℝ (Fin 2) × StdSimplex ℝ (Fin 2) |
      IsBimatrixNash (fun _ _ => 0) (fun _ _ => 0) p.1 p.2}.ncard := by
  have hall : {p : StdSimplex ℝ (Fin 2) × StdSimplex ℝ (Fin 2) |
      IsBimatrixNash (fun _ _ => 0) (fun _ _ => 0) p.1 p.2} = Set.univ := by
    ext p
    simp [IsBimatrixNash, bilinPayoff]
  have : Infinite (StdSimplex ℝ (Fin 2)) :=
    (StdSimplex.equivIcc (R' := ℝ)).infinite_iff.2 (Set.Icc.infinite zero_lt_one)
  rw [hall, Set.ncard_univ, Nat.card_eq_zero_of_infinite]
  exact Nat.not_odd_zero

end MathlibExtTest.GameTheory.LemkeHowson
