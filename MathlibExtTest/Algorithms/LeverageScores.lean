/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.LeverageScores

import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-- The identity matrix has leverage scores summing to its size. -/
example : ∑ i : Fin 2, leverage (fun a b : Fin 2 => if a = b then (1 : ℝ) else 0) i = 2 :=
  leverage_sum (fun a b : Fin 2 => if a = b then (1 : ℝ) else 0) (by
    intro j j'
    fin_cases j <;> fin_cases j' <;> simp [Fin.sum_univ_two])

end
