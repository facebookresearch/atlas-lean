/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Padics.Factorial

/-!
# Tests for factorials in the `p`-adic numbers
-/

@[expose] public section

open Filter Topology

example : Tendsto (fun n : ℕ => (n.factorial : ℚ_[2])) atTop (𝓝 0) :=
  Padic.tendsto_factorial_atTop_nhds_zero 2

/-- Consequence: `‖n!‖ < 1` eventually, in `ℚ_[3]`. -/
example : ∀ᶠ n : ℕ in atTop, ‖(n.factorial : ℚ_[3])‖ < 1 :=
  (Padic.tendsto_factorial_atTop_nhds_zero 3).norm.eventually
    (gt_mem_nhds (by simp))

example : HasSum (fun n : ℕ => (n : ℚ_[3]) * n.factorial) (-1) :=
  Padic.hasSum_mul_factorial 3

/-- The value of the sum: `∑' n, n · n! = -1` in `ℚ_[2]`. -/
example : ∑' n : ℕ, (n : ℚ_[2]) * n.factorial = -1 :=
  (Padic.hasSum_mul_factorial 2).tsum_eq

example : ¬ ∃ f : ℤ_[2] → ℚ_[2], Continuous f ∧ ∀ n : ℕ, f n = (n.factorial : ℚ_[2]) :=
  PadicInt.not_exists_continuous_eq_factorial 2
