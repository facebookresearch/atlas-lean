/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.IntervalCases
import MathlibExt.Combinatorics.Additive.SquareWeightedZeroSum

open MetaMathlibExt

-- `4 = 2 ^ 2` is a nonzero square modulo `5`.
example : (4 : ZMod 5) ∈ squareSet 5 := ⟨by decide, 2, by decide⟩

-- `0 = 0 ^ 2` is a square but is excluded from the nonzero squares, for every modulus.
example (n : ℕ) : (0 : ZMod n) ∉ squareSet n := fun h => h.1 rfl

-- `2` is not a square modulo `5`.
example : (2 : ZMod 5) ∉ squareSet 5 := by
  unfold squareSet
  decide

-- The empty sequence has no weighted zero-sum subsequence: the index set must be nonempty.
example (n : ℕ) (A : Set (ZMod n)) : ¬HasWeightedZeroSumSubseq A ![] := by
  rintro ⟨J, ⟨j, -⟩, -⟩
  exact j.elim0

-- A zero term is a zero-sum subsequence by itself, with the nonzero square weight `1`.
example : HasWeightedZeroSumSubseq (squareSet 5) ![3, 0] :=
  ⟨{1}, Finset.singleton_nonempty 1, fun _ => 1,
    fun _ _ => show (1 : ZMod 5) ∈ squareSet 5 from ⟨by decide, 1, by decide⟩, by simp⟩

-- Not every pair of units works modulo `5`: `1 * 1 + 4 * 1 = 0` with the nonzero squares `1, 4`.
example : HasWeightedZeroSumSubseq (squareSet 5) ![1, 1] := by
  refine ⟨Finset.univ, Finset.univ_nonempty, ![1, 4], ?_, by decide⟩
  intro i _
  fin_cases i
  · exact ⟨by decide, 1, by decide⟩
  · exact ⟨by decide, 2, by decide⟩

-- Explicit units for `n = 15`: `(1, 7)` reduces to `(1, 1)` modulo `3` and to `(1, 2)` modulo `5`,
-- and neither reduction has a square-weighted zero-sum subsequence.
example : IsUnit (7 : ZMod 15) ∧ ∀ p : ℕ, p.Prime → p ∣ 15 →
    ¬HasWeightedZeroSumSubseq (squareSet p)
      (fun i : Fin 2 => (ZMod.cast (![(1 : ZMod 15), 7] i) : ZMod p)) := by
  refine ⟨IsUnit.of_mul_eq_one 13 (by decide), fun p hp hp15 => ?_⟩
  have hp_le : p ≤ 15 := Nat.le_of_dvd (by decide) hp15
  interval_cases p <;> first
    | exact absurd hp (by decide)
    | exact absurd hp15 (by decide)
    | (unfold HasWeightedZeroSumSubseq squareSet; decide)

-- Proposition 17 for `n = 15 = 3 * 5`.
example : ∃ u v : ZMod 15, IsUnit u ∧ IsUnit v ∧
    ∀ p : ℕ, p.Prime → p ∣ 15 →
      ¬HasWeightedZeroSumSubseq (squareSet p)
        (fun i : Fin 2 => (ZMod.cast (![u, v] i) : ZMod p)) :=
  exists_pair_units_avoiding_prime_squareWeights 15 (by decide) (by decide)

-- The base need not be prime. The nonzero term 16 reduces to zero modulo 4².
example : HasWeightedZeroSum (squareSet (4 ^ 4)) (fun _ : Fin 1 => (16 : ZMod (4 ^ 4))) := by
  refine squareWeightedZeroSum_of_reduction_square 4 4 1 (by decide) (by decide)
    (by decide) _ ?_
  refine ⟨fun _ => 1, fun _ => ⟨1, isUnit_one, by simp⟩, ?_⟩
  have hcast : (ZMod.cast (16 : ZMod (4 ^ 4)) : ZMod (4 ^ 2)) = 0 := by decide
  simp [hcast]
