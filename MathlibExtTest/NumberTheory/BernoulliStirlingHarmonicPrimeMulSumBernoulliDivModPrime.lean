/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BernoulliStirlingHarmonicPrimeMulSumBernoulliDivModPrime

/-!
# Concrete prime-scaled Bernoulli sums

The theorem gives denominator control for the value `1 / 2` at `p = 3`, and residue `4`
for the value `11 / 24` at `p = 5`.
-/

namespace MathlibExtTest.NumberTheory.BernoulliStirlingHarmonicPrimeMulSumBernoulliDivModPrime

open MetaMathlibExt

example : ¬3 ∣ (1 / 2 : ℚ).den ∧ ratResidue 3 (1 / 2) = ratResidue 3 (-1) := by
  have hs : ((3 : ℕ) : ℚ) * ∑ j ∈ Finset.range (3 + 1),
      bernoulli j / ((3 - j + 1 : ℕ) : ℚ) = 1 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli_zero, bernoulli_one,
      bernoulli_two, bernoulli_eq_zero_of_odd (show Odd 3 by decide) (by decide)]
    norm_num
  simpa only [hs] using prime_mul_sum_bernoulli_div_mod_prime 3 (by decide) (by decide)

example : ratResidue 5 (11 / 24) = 4 := by
  have hs : ((5 : ℕ) : ℚ) * ∑ j ∈ Finset.range (5 + 1),
      bernoulli j / ((5 - j + 1 : ℕ) : ℚ) = 11 / 24 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli_zero, bernoulli_one,
      bernoulli_two, bernoulli_eq_zero_of_odd (show Odd 3 by decide) (by decide),
      bernoulli_eq_bernoulli'_of_ne_one (show 4 ≠ 1 by decide), bernoulli'_four,
      bernoulli_eq_zero_of_odd (show Odd 5 by decide) (by decide)]
    norm_num
  have h := (prime_mul_sum_bernoulli_div_mod_prime 5 (by decide) (by decide)).2
  rw [hs] at h
  calc
    ratResidue 5 (11 / 24) = ratResidue 5 (-1) := h
    _ = 4 := by norm_num [ratResidue]; decide

end MathlibExtTest.NumberTheory.BernoulliStirlingHarmonicPrimeMulSumBernoulliDivModPrime
