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

section AddTwo

variable (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))

-- For p = 3, p + 2 is prime, and only the powers of two are assumed.
example (htwo : ∀ s : ℕ, 1 ≤ s → f (2 ^ s) = (2 : ℂ) ^ (2 * s)) :
    f 5 = 25 ∧ f 25 = 625 := by
  have hind (q s : ℕ) (hq : q.Prime) (hlt : q < 3) (hs : 1 ≤ s) :
      f (q ^ s) = (q : ℂ) ^ (2 * s) := by
    have : q = 2 := by have := hq.two_le; omega
    subst q
    exact htwo s hs
  have h := MetaMathlibExt.parallelogram_multiplicative_add_two f hf hpar
    (p := 3) (by decide) hind (by decide)
  norm_num at h
  exact h

-- The composite p + 2 = 9 and its square are both powers of a smaller prime.
example (hind : ∀ q s : ℕ, q.Prime → q < 7 → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s)) :
    f 9 = 81 ∧ f 81 = 6561 := by
  have h := MetaMathlibExt.parallelogram_multiplicative_add_two f hf hpar
    (p := 7) (by decide) hind (by decide)
  norm_num at h
  exact h

-- In the prime case 61 = 6² + 5², the doubled product is 60, greater than p.
example (hind : ∀ q s : ℕ, q.Prime → q < 59 → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s)) :
    f 61 = 3721 ∧ f 3721 = 13845841 := by
  have h := MetaMathlibExt.parallelogram_multiplicative_add_two f hf hpar
    (p := 59) (by decide) hind (by decide)
  norm_num at h
  exact h

end AddTwo
