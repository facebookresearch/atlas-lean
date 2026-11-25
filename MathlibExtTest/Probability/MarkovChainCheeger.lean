/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.MarkovChainCheeger
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A reversible two-state chain with unequal stationary masses

The eigenvector `(1, -2)` is positive on the state of mass `2/3`. Only the other
singleton qualifies for the conductance hypothesis, and exactly half its mass leaves.
-/

open Finset Matrix MathlibExt.Probability.MulticommodityFlowWanted

example : (1 / 4 : ℝ) ≤ 1 - (1 / 2) ^ 2 / 2 := by
  let π : Fin 2 → ℝ := ![2 / 3, 1 / 3]
  let P : Matrix (Fin 2) (Fin 2) ℝ := !![3 / 4, 1 / 4; 1 / 2, 1 / 2]
  refine le_one_sub_sq_div_two_of_eigenvector (π := π) (P := P) (f := ![1, -2])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x
    fin_cases x <;> norm_num [π]
  · norm_num [π, Fin.sum_univ_two]
  · rw [mem_rowStochastic_iff_sum]
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num [P]
    · intro i
      fin_cases i <;> norm_num [P, Fin.sum_univ_two]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [π, P]
  · norm_num
  · intro A
    have h : A = ∅ ∨ A = {0} ∨ A = {1} ∨ A = univ := by revert A; decide
    have hc : ({1} : Finset (Fin 2))ᶜ = {0} := by decide
    rcases h with rfl | rfl | rfl | rfl <;> norm_num [π, P, hc, Fin.sum_univ_two]
  · intro h
    have := congrFun h 0
    norm_num at this
  · funext i
    fin_cases i <;> norm_num [P, mulVec, dotProduct, Fin.sum_univ_two]
  · norm_num
