/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OddFibonacciGoldenRatio

open MetaMathlibExt

-- For `k = 1` the identities read `F_3 φ = F_4 + ε` and `F_3 (1 + φ) = F_5 + ε` with
-- `F_3 = 2`, `F_4 = 3`, `F_5 = 5` and `ε = ((√5 - 1)/2)^3`.
example : (2 : ℝ) * Real.goldenRatio = 3 + ((Real.sqrt 5 - 1) / 2) ^ 3 ∧
    (2 : ℝ) * (1 + Real.goldenRatio) = 5 + ((Real.sqrt 5 - 1) / 2) ^ 3 := by
  simpa [Nat.fib_add_two] using fib_odd_mul_goldenRatio 1

-- The error term `((√5 - 1)/2)^(2k+1)` lies in `[0, 1)`, so the identities determine the floors
-- `⌊F_{2k+1} φ⌋ = F_{2k+2}` and `⌊F_{2k+1} (1 + φ)⌋ = F_{2k+3}`.
example (k : ℕ) : ⌊(Nat.fib (2 * k + 1) : ℝ) * Real.goldenRatio⌋₊ = Nat.fib (2 * k + 2) ∧
    ⌊(Nat.fib (2 * k + 1) : ℝ) * (1 + Real.goldenRatio)⌋₊ = Nat.fib (2 * k + 3) := by
  have hlo : 1 < Real.sqrt 5 := by
    rw [Real.lt_sqrt zero_le_one]
    norm_num
  have hhi : Real.sqrt 5 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hε₀ : 0 ≤ ((Real.sqrt 5 - 1) / 2) ^ (2 * k + 1) := pow_nonneg (by linarith) _
  have hε₁ : ((Real.sqrt 5 - 1) / 2) ^ (2 * k + 1) < 1 :=
    pow_lt_one₀ (by linarith) (by linarith) (by omega)
  obtain ⟨h₁, h₂⟩ := fib_odd_mul_goldenRatio k
  rw [h₁, h₂]
  constructor <;> rw [Nat.floor_eq_iff (by positivity)] <;> constructor <;> linarith
