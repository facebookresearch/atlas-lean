/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.Farkas
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

@[expose] public section

/-- Boundary check: the system `x ≤ 0`, `-x ≤ -1` over one
variable is certified infeasible by the multipliers `(1, 1)`:
they combine the constraints to `0 ≤ -1`. -/
example : ¬ ∃ x : Fin 1 → ℚ,
    ∀ i, ∑ j, (![![1], ![-1]] : Fin 2 → Fin 1 → ℚ) i j * x j ≤
      (![0, -1] : Fin 2 → ℚ) i :=
  farkas_infeasible _ _ ![1, 1]
    (fun i => by fin_cases i <;> norm_num)
    (fun j => by fin_cases j <;>
      simp [Fin.sum_univ_two])
    (by simp [Fin.sum_univ_two])
