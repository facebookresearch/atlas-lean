/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.ParallelogramSquareUniqueness
import Mathlib.Tactic.NormNum

-- At the smallest odd prime the induction hypothesis only concerns powers of two.
example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    (htwo : ∀ s : ℕ, 1 ≤ s → f (2 ^ s) = (2 : ℂ) ^ (2 * s))
    (hthree : f 3 = 9) : f 10 = 100 := by
  have hind (q s : ℕ) (hq : q.Prime) (hlt : q < 3) (hs : 1 ≤ s) :
      f (q ^ s) = (q : ℂ) ^ (2 * s) := by
    have : q = 2 := by have := hq.two_le; omega
    subst q
    simpa using htwo s hs
  have h := MetaMathlibExt.parallelogram_multiplicative_sq_add_one f hf hpar
    (p := 3) (by decide) hind (by decide) (by norm_num [hthree])
  norm_num at h
  exact h
