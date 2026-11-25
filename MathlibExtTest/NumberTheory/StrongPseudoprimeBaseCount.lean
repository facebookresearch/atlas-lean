/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.StrongPseudoprimeBaseCount
import Mathlib.Tactic.NormNum.Prime

/-! # Concrete counts of strong pseudoprime bases -/

namespace MetaMathlibExt.card_strongPseudoprime_bases

-- For 9, only 1 and 8 pass. The two extra squarings allowed by 9 - 1 add no bases.
example : {b : ℕ | 1 ≤ b ∧ b < 9 ∧ IsStrongPseudoprime 9 b}.ncard = 2 := by
  have h := card_strongPseudoprime_bases (n := 9) (by decide) (by decide) (by decide)
  have hp : (9 : ℕ).primeFactors = {3} := by decide +kernel
  simp only [hp, Finset.card_singleton, Finset.coe_singleton, Set.image_singleton,
    csInf_singleton, Finset.prod_singleton] at h
  exact_mod_cast h.trans (by decide +kernel : _ = (2 : ℚ))

-- For 65 = 5 × 13, both prime factors allow the second negative-power fiber.
example : {b : ℕ | 1 ≤ b ∧ b < 65 ∧ IsStrongPseudoprime 65 b}.ncard = 6 := by
  have h := card_strongPseudoprime_bases (n := 65) (by decide) (by decide) (by decide)
  have hp : (65 : ℕ).primeFactors = {5, 13} := by decide +kernel
  simp only [hp, Finset.coe_insert, Finset.coe_singleton, Set.image_pair,
    csInf_pair] at h
  exact_mod_cast h.trans (by decide +kernel : _ = (6 : ℚ))

-- For 91 = 7 × 13, the least valuation is one and the odd-part product is nine.
example : {b : ℕ | 1 ≤ b ∧ b < 91 ∧ IsStrongPseudoprime 91 b}.ncard = 18 := by
  have h := card_strongPseudoprime_bases (n := 91) (by decide) (by decide) (by decide)
  have hp : (91 : ℕ).primeFactors = {7, 13} := by decide +kernel
  simp only [hp, Finset.coe_insert, Finset.coe_singleton, Set.image_pair,
    csInf_pair] at h
  exact_mod_cast h.trans (by decide +kernel : _ = (18 : ℚ))

end MetaMathlibExt.card_strongPseudoprime_bases
