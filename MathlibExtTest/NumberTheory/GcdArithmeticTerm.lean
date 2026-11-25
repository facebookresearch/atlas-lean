/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GcdArithmeticTerm

/-!
# Boundary cases for the gcd-term sequence and the double-remainder formula
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

example (n : ℕ) : (gcdTermSeq 4 6 n).den = 1 := by
  obtain ⟨m, hm⟩ := (gcdTermSeq_natural_and_eq_gcd_add_one 4 6 (by decide) (by decide)).1 n
  simp [hm]

example : gcdTermSeq 4 6 24 = 3 := by
  have h := (gcdTermSeq_natural_and_eq_gcd_add_one 4 6 (by decide) (by decide)).2
  norm_num at h
  exact h

example : gcdTermSeq 1 1 1 = 2 := by
  have h := (gcdTermSeq_natural_and_eq_gcd_add_one 1 1 le_rfl le_rfl).2
  norm_num at h
  exact h

-- Both inputs are minimal, so the two remainders are taken modulo 16 and 5.
example : (-125 : ℤ) % 16 % 5 = 3 := by
  have h := gcd_eq_neg_emod_emod_five_sub_two 1 1 le_rfl le_rfl
  change (1 : ℤ) = (-125 : ℤ) % 16 % 5 - 2 at h
  omega

-- On the diagonal both factors of the first modulus coincide.
example (a : ℕ) (ha : 1 ≤ a) :
    (-(5 : ℤ) ^ (a ^ 2 * (a ^ 2 + a + a))) %
      (((5 : ℤ) ^ (a ^ 3) - 1) ^ 2) % (5 : ℤ) ^ (a ^ 2) = (a : ℤ) + 2 := by
  have h := gcd_eq_neg_emod_emod_five_sub_two a a ha ha
  rw [Nat.gcd_self] at h
  ring_nf at h ⊢
  omega
