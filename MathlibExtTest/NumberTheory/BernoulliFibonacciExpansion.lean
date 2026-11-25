/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.BernoulliFibonacciExpansion
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MathlibExt.NumberTheory.FiniteSumsFibLucasWanted

-- The definitions are exposed and agree with `√5` and Mathlib's golden ratio and its conjugate.
example : sqrt5 = Real.sqrt 5 := rfl

example : fibAlpha = Real.goldenRatio := rfl

example : fibBeta = Real.goldenConj := rfl

-- `α - β = √5` and `α β = -1`.
example : fibAlpha - fibBeta = sqrt5 :=
  Real.goldenRatio_sub_goldenConj

example : fibAlpha * fibBeta = -1 :=
  Real.goldenRatio_mul_goldenConj

-- With `s = 0` no falling factorial is left: the identity is the expansion of `(x + β)^m`.
example (m : ℕ) (x : ℝ) :
    (x + fibBeta) ^ m =
      ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 5) ^ k * (Nat.choose n k : ℝ) * (Nat.choose m n : ℝ) * (bernoulli k : ℝ) *
          ((Nat.fib (n - k + 1) : ℝ) / (n - k + 1 : ℕ)) * x ^ (m - n) := by
  simpa using descFactorial_mul_add_fibBeta_pow m 0 (Nat.zero_le m) x

-- With `s = m` only the term `n = 0` survives, and the double sum is `m!` for every `x`.
example (m : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 5) ^ k * (Nat.choose n k : ℝ) * (Nat.choose m n : ℝ) * (bernoulli k : ℝ) *
          ((Nat.fib (n - k + 1) : ℝ) / (n - k + 1 : ℕ)) *
          (Nat.descFactorial (m - n) m : ℝ) * x ^ (m - n - m) = m.factorial := by
  rw [← descFactorial_mul_add_fibBeta_pow m m le_rfl x]
  simp [Nat.descFactorial_self]

-- For `m = 2` and `s = 1`, the double sum evaluated term by term is `2x + 1 - √5 = 2(x + β)`, the
-- derivative of `(x + β)^2`; the term `n = 2` vanishes since `Nat.descFactorial 0 1 = 0`.
example (x : ℝ) :
    ∑ n ∈ Finset.range 3, ∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 5) ^ k * (Nat.choose n k : ℝ) * (Nat.choose 2 n : ℝ) * (bernoulli k : ℝ) *
          ((Nat.fib (n - k + 1) : ℝ) / (n - k + 1 : ℕ)) *
          (Nat.descFactorial (2 - n) 1 : ℝ) * x ^ (2 - n - 1) = 2 * x + 1 - Real.sqrt 5 := by
  norm_num [Finset.sum_range_succ, bernoulli_one]
  ring

end MathlibExt.NumberTheory.FiniteSumsFibLucasWanted
