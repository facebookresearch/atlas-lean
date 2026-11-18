/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.BoostingMinimax

/-!
# Tests for weak learnability and the minimax theorem

A non-degenerate example: three instances and three hypotheses, hypothesis `j` erring exactly on
the instance `j`. Every distribution on the instances gives some hypothesis weighted error at most
`1 / 3 = 1 / 2 - 1 / 6` (the one erring on a lightest instance), so the hypotheses of the theorems
hold with `γ = 1 / 6`, and the target is recovered as a weighted majority vote.
-/

namespace Cslib.MachineLearning.BoostingMinimax

open Convexity

/-- Hypothesis `j` flips the target on instance `j` only. -/
def flipOne (c : Fin 3 → Bool) (j : Fin 3) (x : Fin 3) : Bool := if x = j then !c x else c x

theorem weak_flipOne (c : Fin 3 → Bool) (Q : StdSimplex ℝ (Fin 3)) :
    ∃ j, ∑ x, Q.weights x * (if flipOne c j x = c x then 0 else 1) ≤ 1 / 2 - 1 / 6 := by
  obtain ⟨j, -, hj⟩ := Finset.univ.exists_min_image (fun x => Q.weights x) Finset.univ_nonempty
  refine ⟨j, ?_⟩
  have hsum : ∑ x, Q.weights x * (if flipOne c j x = c x then 0 else 1) = Q.weights j := by
    rw [Finset.sum_eq_single j]
    · simp [flipOne]
    · intro b _ hb; simp [flipOne, hb]
    · simp
  have htot := Q.total_of_fintype
  rw [Fin.sum_univ_three] at htot
  have h0 := hj 0 (Finset.mem_univ _)
  have h1 := hj 1 (Finset.mem_univ _)
  have h2 := hj 2 (Finset.mem_univ _)
  rw [hsum]
  linarith

example (c : Fin 3 → Bool) : ∃ P : StdSimplex ℝ (Fin 3),
    ∀ x, ∑ j, P.weights j * (if flipOne c j x = c x then 0 else 1) ≤ 1 / 2 - 1 / 6 :=
  exists_forall_mistake_le (by norm_num) (flipOne c) c (weak_flipOne c)

example (c : Fin 3 → Bool) : ∃ P : StdSimplex ℝ (Fin 3), ∀ x,
    1 / 2 + 1 / 6 ≤ ∑ j, P.weights j * (if flipOne c j x = c x then 1 else 0) ∧
      weightedVote (fun j => P.weights j) (flipOne c) x = c x :=
  exists_weightedVote_eq (by norm_num) (flipOne c) c (by norm_num) (weak_flipOne c)

-- the mistake matrix of this instance is `1` exactly on the diagonal
example (c : Fin 3 → Bool) (x j : Fin 3) :
    mistakeMatrix (flipOne c) c x j = if x = j then 1 else 0 := by
  by_cases h : x = j <;> simp [mistakeMatrix, flipOne, h]

#print axioms exists_forall_mistake_le
#print axioms exists_weightedVote_eq

end Cslib.MachineLearning.BoostingMinimax
