/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.ParallelogramSquareUniquenessParallelogramMultiplicativeFiveKAddThree
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the parallelogram identity at five times k plus three

Concrete consequences at `p = 19`, `k = 5` and at `p = 151`, `k = 38`.
-/

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.ParallelogramSquareUniquenessParallelogramMultiplicativeFiveKAddThree

example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    (hind : ∀ q s : ℕ, q.Prime → q < 19 → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s)) :
    f 28 = 784 := by
  convert MetaMathlibExt.parallelogram_multiplicative_five_k_add_three f hf hpar
    (p := 19) (by norm_num) hind (k := 5) (by norm_num) (by norm_num) (by norm_num) using 1
  norm_num

example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    (hind : ∀ q s : ℕ, q.Prime → q < 151 → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s)) :
    f 193 = 37249 := by
  convert MetaMathlibExt.parallelogram_multiplicative_five_k_add_three f hf hpar
    (p := 151) (by norm_num) hind (k := 38) (by norm_num) (by norm_num) (by norm_num) using 1
  norm_num

end MathlibExtTest.NumberTheory.ArithmeticFunction.ParallelogramSquareUniquenessParallelogramMultiplicativeFiveKAddThree
