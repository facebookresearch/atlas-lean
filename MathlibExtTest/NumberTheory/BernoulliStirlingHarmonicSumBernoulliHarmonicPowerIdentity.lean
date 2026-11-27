/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BernoulliStirlingHarmonicSumBernoulliHarmonicPowerIdentity

namespace MathlibExtTest.NumberTheory.BernoulliStirlingHarmonicSumBernoulliHarmonicPowerIdentity

open Finset

-- The first two harmonic numbers, for evaluating the identity at small arguments.
private theorem harmonic_one_eq : harmonic 1 = 1 := by
  simp [harmonic]

private theorem harmonic_two_eq : harmonic 2 = 3 / 2 := by
  simp [harmonic, sum_range_succ]
  norm_num

-- At (n, m) = (2, 1), the identity determines the sign convention for B₁.
example : bernoulli 1 = -1 / 2 := by
  have h := MetaMathlibExt.sum_bernoulli_harmonic_power_identity 2 1 (by decide) (by decide)
  rw [show Icc 1 2 = {1, 2} by decide, sum_pair (by decide : (1 : ℕ) ≠ 2), Icc_self,
    sum_singleton] at h
  norm_num only [Nat.choose_one_right, Nat.choose_self, Nat.cast_ofNat, Nat.cast_one,
    div_one, pow_one, harmonic_one_eq, harmonic_two_eq] at h
  linarith only [h]

-- At (n, m) = (1, 2), the left side vanishes and the identity gives H₂.
example : harmonic 2 = 3 / 2 := by
  have h := MetaMathlibExt.sum_bernoulli_harmonic_power_identity 1 2 (by decide) (by decide)
  rw [Icc_self, sum_singleton, show Icc 1 2 = {1, 2} by decide,
    sum_pair (by decide : (1 : ℕ) ≠ 2)] at h
  norm_num only [Nat.choose_self, Nat.cast_ofNat, Nat.cast_one, div_one, pow_one,
    harmonic_one_eq] at h
  linarith only [h]

end MathlibExtTest.NumberTheory.BernoulliStirlingHarmonicSumBernoulliHarmonicPowerIdentity
