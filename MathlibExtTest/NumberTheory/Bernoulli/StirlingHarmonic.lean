/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Bernoulli.StirlingHarmonic

namespace MetaMathlibExt.sum_stirling_harmonic_eq_bernoulli

open Finset

-- The zeroth column vanishes, even though the sum includes the term at k = 0.
example (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Icc 0 n, (-1 : ℚ) ^ (k - 0) * (Nat.stirlingSecond n k : ℚ) *
      (Nat.stirlingFirst k 0 : ℚ) * harmonic k) = 0 := by
  rw [sum_stirling_harmonic_eq_bernoulli (hjn := hn)]
  simp

-- The first off-diagonal case uses the negative convention for B₁.
example :
    (∑ k ∈ Icc 1 2, (-1 : ℚ) ^ (k - 1) * (Nat.stirlingSecond 2 k : ℚ) *
      (Nat.stirlingFirst k 1 : ℚ) * harmonic k) = -1 / 2 := by
  rw [sum_stirling_harmonic_eq_bernoulli 2 1 (by decide)]
  norm_num [Nat.choose_one_right, bernoulli_one]

-- A gap of two exercises the nonzero B₂ term and a binomial coefficient greater than two.
example :
    (∑ k ∈ Icc 2 4, (-1 : ℚ) ^ (k - 2) * (Nat.stirlingSecond 4 k : ℚ) *
      (Nat.stirlingFirst k 2 : ℚ) * harmonic k) = 5 / 12 := by
  rw [sum_stirling_harmonic_eq_bernoulli 4 2 (by decide)]
  norm_num [show Nat.choose 4 2 = 6 by decide, bernoulli_two]

end MetaMathlibExt.sum_stirling_harmonic_eq_bernoulli
