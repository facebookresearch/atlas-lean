/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GcdArithmeticTerm

/-!
# Boundary cases for the gcd-term sequence
-/

open MetaMathlibExt

example (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    gcdTermSeq a b 0 = gcdTermSeq 1 1 0 := by
  rw [gcdTermSeq_zero a b ha hb, gcdTermSeq_zero 1 1 le_rfl le_rfl]

example (n : ℕ) : gcdTermSeq 1 2 (n + 1) < (n : ℚ) + 2 := by
  obtain ⟨hle, hval, heq⟩ :=
    gcdTermSeq_le_gcdTermSeq_one_one 1 2 le_rfl (by decide) (Or.inr (by decide)) (n + 1)
  have hlt := lt_of_le_of_ne hle fun h => Nat.succ_ne_zero n (heq h)
  simpa [hval, add_assoc, one_add_one_eq_two] using hlt

example (d n : ℕ) : gcdTermSeq 0 d n = 0 ∧ gcdTermSeq d 0 n = 0 := by
  simp [gcdTermSeq]
