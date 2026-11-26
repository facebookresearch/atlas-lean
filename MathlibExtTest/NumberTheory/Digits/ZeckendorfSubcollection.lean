/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ZeckendorfSubcollection

/-! # Tests for counting a Zeckendorf subcollection -/

namespace MetaMathlibExtTest.ZeckendorfSubcollection

open MetaMathlibExt

-- Only zero and the first basis digit lie strictly below two copies of that digit.
private theorem pred_two {E : Set (ℕ →₀ ℕ)} (h : Finsupp.single 0 1 ∈ E) :
    IsImmediatePredecessor E (Finsupp.single 0 2) (Finsupp.single 0 1) := by
  refine ⟨h, ⟨0, by simp, fun j hj => by simp [hj.ne']⟩, ?_⟩
  rintro z _ ⟨i, hi, hgt⟩
  have hi0 : i = 0 := by
    by_contra hne
    simp [Ne.symm hne] at hi
  subst i
  simp only [Finsupp.single_eq_same] at hi
  have hz (j : ℕ) (hj : 0 < j) : z j = 0 := by simpa [hj.ne'] using hgt j hj
  rcases (Nat.lt_succ_iff.mp hi).eq_or_lt with hone | hzero
  · left
    ext j
    obtain rfl | hj := Nat.eq_zero_or_pos j
    · simpa using hone
    · simp [hj.ne', hz _ hj]
  · exact Or.inr ⟨0, by simpa using hzero, fun j hj => by simp [hj.ne', hz _ hj]⟩

-- With ternary weights, a subcollection that steps from the first unit to the second
-- basis digit represents precisely 0 and 1 below the strict upper endpoint 3.
example {E E' : Set (ℕ →₀ ℕ)} (hE : IsZeckendorfCollection E)
    (hE' : IsZeckendorfCollection E') (hsub : E ⊆ E')
    (hbij : Set.BijOn (zeckendorfEval (3 ^ ·)) E' Set.univ)
    (htwo : Finsupp.single 0 2 ∈ E')
    (hstep : IsImmediateSuccessor E (Finsupp.single 0 1) (Finsupp.single 1 1)) :
    {n : ℕ | n < 3 ∧ ∃ z ∈ E, zeckendorfEval (3 ^ ·) z = n} = {0, 1} := by
  have hcut := subcollectionLT_eval_eq_eval_bar hE hE' hsub
    (fun _ _ h => Nat.pow_lt_pow_right (by decide : 1 < 3) h) (fun _ => Nat.pow_pos (by decide))
    hbij htwo
    (by simp) (pred_two (hE.2.1 0)) hstep
  have hval (k a : ℕ) : zeckendorfEval (3 ^ ·) (Finsupp.single k a) = a * 3 ^ k := by
    simp [zeckendorfEval]
  simp only [hval, pow_zero, mul_one, pow_one, one_mul] at hcut
  rw [← hcut]
  ext n
  constructor
  · rintro ⟨hlt, _⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · rintro (rfl | h)
    · exact ⟨by decide, 0, hE.1, by simp [zeckendorfEval]⟩
    · obtain rfl : n = 1 := h
      exact ⟨by decide, Finsupp.single 0 1, hE.2.1 0, by simp [hval]⟩

end MetaMathlibExtTest.ZeckendorfSubcollection
