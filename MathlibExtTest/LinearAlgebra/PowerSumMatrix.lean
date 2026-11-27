/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.LinearAlgebra.PowerSumMatrix

open MathlibExt.LinearAlgebra.PowerSumMatrixWanted

-- At the smallest admissible m, both formulas recover the classical trace identities.
example (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (M ^ 2).trace = M.trace ^ 2 - 2 * M.det ∧
      (M ^ 3).trace = M.trace ^ 3 - 3 * M.det * M.trace := by
  obtain ⟨he, ho⟩ := trace_pow_two M 1 le_rfl
  norm_num [Finset.sum_range_succ, Nat.factorial] at he ho
  constructor
  · rw [he]
    ring
  · rw [ho]
    ring

-- With zero trace, only the top coefficient survives in the even formula.
example (M : Matrix (Fin 2) (Fin 2) ℝ) (ht : M.trace = 0) :
    (M ^ 4).trace = 2 * M.det ^ 2 ∧ (M ^ 5).trace = 0 := by
  obtain ⟨he, ho⟩ := trace_pow_two M 2 (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial, ht] at he ho
  refine ⟨?_, ho⟩
  rw [he]
  ring
