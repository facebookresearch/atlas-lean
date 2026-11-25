/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.LinearAlgebra.Matrix.RowStochasticBounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Test a rectangular matrix with a singleton-support row and a separate zero row. -/

open Matrix
open scoped BigOperators

private def weights : Matrix (Fin 2) (Fin 3) ℝ := fun i j => if i = 0 then ![0, 1, 0] j else 0

private def values : Fin 3 → ℝ := ![-10, 7, 20]

example (j : Fin 3) : weights 1 j = 0 := by simp [weights]

example : (weights *ᵥ values) 0 = 7 := by
  have hW (i : Fin 2) (j : Fin 3) : 0 ≤ weights i j := by
    fin_cases i <;> fin_cases j <;> norm_num [weights]
  have hsum : ∑ j, weights 0 j = 1 := by
    norm_num [weights, Fin.sum_univ_three]
  have honly (j : Fin 3) (hj : 0 < weights 0 j) : j = 1 := by
    fin_cases j
    · norm_num [weights] at hj
    · rfl
    · norm_num [weights] at hj
  obtain ⟨lo, hi, hlo, hhi, _, hl, hh⟩ :=
    exists_mulVec_bounds_of_sum_row_eq_one 0 hW hsum values
  rw [honly lo hlo] at hl
  rw [honly hi hhi] at hh
  exact le_antisymm (by simpa [values] using hh) (by simpa [values] using hl)
