/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.MoebiusGeometricGrowth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace MetaMathlibExt.MoebiusGeometricGrowthTest

open scoped ArithmeticFunction.Moebius

-- At the threshold the positive-index hypotheses allow an arbitrary negative value at zero.
example (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ ∑ d ∈ n.divisors, (μ (n / d) : ℝ) *
      (if d = 0 then -1 else (1221 / 1000 : ℝ) ^ d) := by
  apply moebius_conv_nonneg_of_geometric_growth _ _ (1221 / 1000) le_rfl _ n hn
  · intro k hk
    rw [ite_eq_right (by omega : k ≠ 0)]
    positivity
  · intro k hk
    simp [show k ≠ 0 by omega, pow_succ, mul_comm]

-- At six, when the first term vanishes, the sixth term covers both negative contributions.
example (b : ℕ → ℝ) (hb : ∀ n, 1 ≤ n → 0 ≤ b n) (h₁ : b 1 = 0)
    (hg : ∀ n, 1 ≤ n → (1221 / 1000 : ℝ) * b n ≤ b (n + 1)) :
    b 2 + b 3 ≤ b 6 := by
  have h := moebius_conv_nonneg_of_geometric_growth b hb _ le_rfl hg 6 (by decide)
  have divisors : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  norm_num [divisors, h₁, ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three, ArithmeticFunction.moebius_apply_one]
    at h
  linarith

end MetaMathlibExt.MoebiusGeometricGrowthTest
