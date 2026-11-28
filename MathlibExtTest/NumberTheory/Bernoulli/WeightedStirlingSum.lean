/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.Bernoulli.WeightedStirlingSum

open MathlibExt.NumberTheory.BernoulliSecondKindWanted

-- At n = 0, only the empty partition contributes.
example (r : ℕ) (hr : 1 ≤ r) :
    1 / (r : ℚ) = (1 / ((r - 1).factorial : ℚ)) *
      ∑ k ∈ Finset.range r, (Nat.stirlingFirst r (k + 1) : ℚ) * bernoulli k := by
  simpa using sum_stirlingSecond_div_add r 0 hr

-- The first shift beyond the classical Bernoulli formula gives two consecutive terms.
example (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k *
        ((k.factorial : ℚ) / (k + 2)) * (Nat.stirlingSecond n k : ℚ) =
      bernoulli n + bernoulli (n + 1) := by
  simpa [Finset.sum_range_succ, Nat.stirlingFirst] using
    sum_stirlingSecond_div_add 2 n (by decide)
