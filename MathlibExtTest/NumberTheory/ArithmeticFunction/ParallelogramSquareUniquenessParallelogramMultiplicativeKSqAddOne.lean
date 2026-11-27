/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.ParallelogramSquareUniquenessParallelogramMultiplicativeKSqAddOne
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.ParallelogramSquareUniquenessParallelogramMultiplicativeKSqAddOne

-- At `p = 7` (`k = 2`) the lemma determines `f` at `5` and `17`.
example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    (hind : ∀ q s : ℕ, q.Prime → q < 7 → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s)) :
    f 5 = 25 ∧ f 17 = 289 := by
  have h := MetaMathlibExt.parallelogram_multiplicative_k_sq_add_one f hf hpar
    (p := 7) (by decide) hind (k := 2) (by norm_num)
  norm_num at h
  exact h

-- At `p = 3` (`k = 1`) the lemma determines `f` at `2` and `5`.
example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    (hind : ∀ q s : ℕ, q.Prime → q < 3 → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s)) :
    f 2 = 4 ∧ f 5 = 25 := by
  have h := MetaMathlibExt.parallelogram_multiplicative_k_sq_add_one f hf hpar
    (p := 3) (by decide) hind (k := 1) (by norm_num)
  norm_num at h
  exact h

end MathlibExtTest.NumberTheory.ArithmeticFunction.ParallelogramSquareUniquenessParallelogramMultiplicativeKSqAddOne
