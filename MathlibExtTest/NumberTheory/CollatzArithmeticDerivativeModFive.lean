/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CollatzArithmeticDerivativeModFive

namespace MathlibExtTest.NumberTheory.CollatzArithmeticDerivativeModFive

open MetaMathlibExt

-- The example `71 * 1609` and `349 * 491` realizes both residue orders.
example : (71 % 5 = 1 ∧ 1609 % 5 = 4) ∧ (491 % 5 = 1 ∧ 349 % 5 = 4) := by
  obtain ⟨h₁, h₂⟩ := isCompatibleSemiprimePair_71_1609.mod_five
  exact ⟨h₁.resolve_right (by decide), h₂.resolve_left (by decide)⟩

-- Both semiprime products are `4` modulo `5`.
example {p q r s : ℕ} (h : IsCompatibleSemiprimePair p q r s) :
    (p * q) % 5 = 4 ∧ (r * s) % 5 = 4 := by
  obtain ⟨hpq, hrs⟩ := h.mod_five
  refine ⟨?_, ?_⟩ <;> rw [Nat.mul_mod]
  · rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  · rcases hrs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

end MathlibExtTest.NumberTheory.CollatzArithmeticDerivativeModFive
