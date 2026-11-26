/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.ParallelogramSquareUniquenessParallelogramMultiplicativeSixKAddOne
import Mathlib.Tactic.NormNum

/-!
# Tests for the parallelogram induction value at 6k + 1

The cases `p = 19`, `p = 23`, and `p = 31` give the square values at `31`, `37`, and `49`.
-/

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.ParallelogramSquareUniquenessParallelogramMultiplicativeSixKAddOne

example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    (hind : ∀ q s : ℕ, q.Prime → q < 19 → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s)) :
    f 31 = 961 := by
  convert MetaMathlibExt.parallelogram_multiplicative_six_k_add_one f hf hpar
    (p := 19) (by decide) hind (k := 5) (by decide) (by decide) (by decide) using 1
  norm_num

example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    (hind : ∀ q s : ℕ, q.Prime → q < 23 → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s)) :
    f 37 = 1369 := by
  convert MetaMathlibExt.parallelogram_multiplicative_six_k_add_one f hf hpar
    (p := 23) (by decide) hind (k := 6) (by decide) (by decide) (by decide) using 1
  norm_num

example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    (hind : ∀ q s : ℕ, q.Prime → q < 31 → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s)) :
    f 49 = 2401 := by
  convert MetaMathlibExt.parallelogram_multiplicative_six_k_add_one f hf hpar
    (p := 31) (by decide) hind (k := 8) (by decide) (by decide) (by decide) using 1
  norm_num

end MathlibExtTest.NumberTheory.ArithmeticFunction.ParallelogramSquareUniquenessParallelogramMultiplicativeSixKAddOne
