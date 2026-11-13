/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Gamma.AscPochhammer

/-! Tests for `MathlibExt.Analysis.SpecialFunctions.Gamma.AscPochhammer`. -/

-- A positive argument: `Γ(1 + 2) = (1 · 2) · Γ(1) = 2`.
example : Real.Gamma (1 + ((2 : ℕ) : ℝ)) = 2 := by
  rw [Real.Gamma_add_nat_eq (fun j => by positivity), Real.Gamma_one, mul_one]
  simp [ascPochhammer_succ_eval]
  norm_num

-- The hypothesis also admits negative non-integer arguments:
-- `Γ(-1/2 + 1) = (-1/2) · Γ(-1/2)`.
example : Real.Gamma (-1 / 2 + ((1 : ℕ) : ℝ)) = -1 / 2 * Real.Gamma (-1 / 2) := by
  have h : ∀ j : ℕ, (-1 / 2 : ℝ) + j ≠ 0 := by
    intro j hj
    have h2 : (2 * j : ℝ) = 1 := by linarith
    have h3 : 2 * j = 1 := by exact_mod_cast h2
    omega
  rw [Real.Gamma_add_nat_eq h]
  simp
