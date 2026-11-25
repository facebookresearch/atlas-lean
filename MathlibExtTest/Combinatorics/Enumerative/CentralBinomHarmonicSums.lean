/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CentralBinomHarmonicSums

open MetaMathlibExt

-- The k = 0 term contributes the initial weight at exponent zero.
example (a : ℕ → ℚ) : centralBinomPowSum a 0 0 = a 0 := by
  simp [centralBinomPowSum_zero]

-- At n = 2 the three powers give distinct values.
example : centralBinomPowSum harmonic 1 2 = 13 / 8 ∧
    centralBinomPowSum harmonic 2 2 = 11 / 4 ∧ centralBinomPowSum harmonic 3 2 = 5 := by
  obtain ⟨h₁, h₂, h₃⟩ := centralBinomPowSum_harmonic_one_two_three 2
  norm_num [harmonic_succ, Nat.centralBinom, Nat.choose] at h₁ h₂ h₃ ⊢
  exact ⟨h₁, h₂, h₃⟩

-- The odd harmonic weight at k = 2 is 4/3, giving three different rational sums.
example : centralBinomPowSum oddHarmonic 1 2 = 3 / 2 ∧
    centralBinomPowSum oddHarmonic 2 2 = 5 / 2 ∧ centralBinomPowSum oddHarmonic 3 2 = 9 / 2 := by
  obtain ⟨h₁, h₂, h₃⟩ := centralBinomPowSum_oddHarmonic_one_two_three 2
  norm_num [oddHarmonic_succ, Nat.centralBinom, Nat.choose] at h₁ h₂ h₃ ⊢
  exact ⟨h₁, h₂, h₃⟩
