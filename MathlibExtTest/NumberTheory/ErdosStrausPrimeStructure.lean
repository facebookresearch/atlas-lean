/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosStrausPrimeStructure
import Mathlib.Tactic.NormNum

/-! # Examples of Chamberland's divisor criterion -/

open MathlibExt.NumberTheory.ErdosStrausPrimeStructureWanted

-- The smallest prime admits a repeated denominator in (1, 2, 2).
example : ∃ q r s₁ s₂ : ℕ, 0 < q ∧ 0 < r ∧ 0 < s₁ ∧ 0 < s₂ ∧
    q % 4 = 3 ∧ s₁ ∣ (q + 1) / 4 ∧ s₂ ∣ (q + 1) / 4 ∧ 2 + 4 * s₁ * s₂ = q * r := by
  apply (erdos_straus_prime_restricted_representation_iff 2 (by decide)).mp
  exact ⟨1, 2, 2, by norm_num⟩

-- For p = 17 the two divisors can both equal 6. Their product divides 6².
example : ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ≤ b ∧ b ≤ c ∧
    ¬17 ∣ a ∧ 17 ∣ b ∧ 17 ∣ c ∧ (4 : ℚ) / 17 = 1 / a + 1 / b + 1 / c := by
  apply (erdos_straus_prime_restricted_representation_iff 17 (by decide)).mpr
  exact ⟨23, 7, 6, 6, by decide⟩
