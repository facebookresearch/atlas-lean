/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.BernoulliFibonacciVanishing
import Mathlib.Tactic.NormNum

namespace MathlibExt.NumberTheory.FiniteSumsFibLucasWanted

-- At the first admissible exponent, the two outer terms cancel.
example :
    ∑ n ∈ Finset.range (1 + 1), ∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 5) ^ k * (Nat.choose n k : ℝ) *
          (Nat.choose 1 n : ℝ) * (bernoulli k : ℝ) *
          ((Nat.fib (n - k + 1) : ℝ) / (n - k + 1 : ℕ)) *
          (-fibBeta) ^ (1 - n) = 0 :=
  sum_bernoulli_fib_neg_fibBeta 1 le_rfl

-- At exponent zero, the sole term is one.
example :
    ∑ n ∈ Finset.range (0 + 1), ∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 5) ^ k * (Nat.choose n k : ℝ) *
          (Nat.choose 0 n : ℝ) * (bernoulli k : ℝ) *
          ((Nat.fib (n - k + 1) : ℝ) / (n - k + 1 : ℕ)) *
          (-fibBeta) ^ (0 - n) = 1 := by
  norm_num [Nat.fib_one]

end MathlibExt.NumberTheory.FiniteSumsFibLucasWanted
