/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AscentSequenceBinomialFibonacci

namespace MetaMathlibExt

private def binomialSum (n : ℕ) : ℕ :=
  (∑ k ∈ Finset.Icc 1 (n / 3 - 1),
    (Nat.choose (n - k - 4) (2 * k) * 2 ^ (n - 3 * k - 4) +
      Nat.choose (n - k - 4) (2 * k - 1) * 2 ^ (n - 3 * k - 3))) + 2 ^ (n - 4)

example (n : ℕ) (hn : 4 ≤ n) : binomialSum n = Nat.fib (2 * n - 7) :=
  sum_choose_mul_two_pow_add_two_pow_eq_fib n hn

-- Both empty sums at the lower endpoint.
example : binomialSum 4 = 1 ∧ binomialSum 5 = 2 := by decide

-- The first nonempty sum has a vanishing even term at its upper endpoint.
example : binomialSum 6 = 5 := by decide

-- Both terms at the upper endpoint are nonzero.
example : binomialSum 8 = 34 := by decide

-- A multiple of three with more than one index: the last odd term is still 1.
example : binomialSum 9 = 89 := by decide

end MetaMathlibExt
