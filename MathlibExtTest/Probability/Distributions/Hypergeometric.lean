/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.Hypergeometric

@[expose] public section

open Finset ProbabilityTheory

namespace MathlibExtTest.Probability.Distributions.Hypergeometric

/-- Two draws from an urn of `5` items with `2` marked: `P(k = 1) = C(2,1) C(3,1) / C(5,2)`. -/
example : hypergeometricReal 5 2 2 1 = 3 / 5 := by
  norm_num [hypergeometricReal, Nat.choose]

/-- Both marked items drawn: `P(k = 2) = 1 / 10`. -/
example : hypergeometricReal 5 2 2 2 = 1 / 10 := by
  norm_num [hypergeometricReal, Nat.choose]

/-- Boundary: more successes than draws, or than marked items, has probability `0`. -/
example : hypergeometricReal 5 2 2 3 = 0 := hypergeometricReal_of_lt (by norm_num)

example : hypergeometricReal 10 1 5 2 = 0 := hypergeometricReal_of_lt' (by norm_num)

/-- Boundary: drawing the whole urn gives `K` marked items surely. -/
example : hypergeometricReal 4 3 4 3 = 1 := by
  norm_num [hypergeometricReal]

/-- Boundary: no draws gives `k = 0` surely. -/
example : hypergeometricReal 7 3 0 0 = 1 := by
  norm_num [hypergeometricReal]

/-- Junk value outside the domain `n ≤ N`: with `3` draws from `2` items `C(2, 3) = 0`, so the
mass function is `0` (it is not a probability there). -/
example : hypergeometricReal 2 1 3 1 = 0 := by
  norm_num [hypergeometricReal]

/-- Normalization and mean for `N = 5`, `K = 2`, `n = 2`: mean `n K / N = 4 / 5`. -/
example : ∑ k ∈ range 3, hypergeometricReal 5 2 2 k = 1 :=
  sum_hypergeometricReal (by norm_num) (by norm_num)

example : ∑ k ∈ range 3, (k : ℝ) * hypergeometricReal 5 2 2 k = 2 * 2 / 5 := by
  exact_mod_cast sum_mul_hypergeometricReal (N := 5) (K := 2) (n := 2) (by norm_num)
    (by norm_num) (by norm_num)

/-- Direct evaluation of the mean agrees with `sum_mul_hypergeometricReal`. -/
example : ∑ k ∈ range 3, (k : ℝ) * hypergeometricReal 5 2 2 k = 4 / 5 := by
  norm_num [Finset.sum_range_succ, hypergeometricReal, Nat.choose]

/-- The `PMF` assigns the hypergeometric mass. -/
example : hypergeometric 5 2 2 (by norm_num) (by norm_num) 1 = ENNReal.ofReal (3 / 5) := by
  rw [hypergeometric_apply]
  norm_num [hypergeometricReal, Nat.choose]

end MathlibExtTest.Probability.Distributions.Hypergeometric
