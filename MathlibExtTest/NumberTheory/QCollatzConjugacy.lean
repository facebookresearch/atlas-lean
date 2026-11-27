/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QCollatzConjugacy

/-! # Tests for the q-Collatz conjugacy -/

open MetaMathlibExt PowerSeries

-- Transport the 2-cycle, checking both branches on the 2-adic side and distinctness.
example :
    ∃ a b : PowerSeries (ZMod 2), a ≠ b ∧
      qCollatz (1 + X) 1 a = b ∧ qCollatz (1 + X) 1 b = a := by
  obtain ⟨h, hh⟩ := qCollatz_one_add_X_conjugate_twoAdicCollatz
  obtain ⟨h₁, h₂⟩ := twoAdicCollatz_one_two
  have hne : (1 : ℤ_[2]) ≠ 2 := by norm_num
  refine ⟨h 1, h 2, fun hab => hne (h.injective hab), ?_, ?_⟩
  · simpa only [Equiv.apply_symm_apply, h₁] using congrArg h (hh 1)
  · simpa only [Equiv.apply_symm_apply, h₂] using congrArg h (hh 2)

-- The conjugacy sends the 2-adic 2-cycle `{1, 2}` to a 2-cycle of `qCollatz 1 1`.
example : ∃ h : ℤ_[2] ≃ PowerSeries (ZMod 2),
    qCollatz 1 1 (h 1) = h 2 ∧ qCollatz 1 1 (h 2) = h 1 := by
  obtain ⟨h, hh⟩ := qCollatz_conjugate_twoAdicCollatz 1 1 (by simp) (by simp)
  have h12 := twoAdicCollatz_one_two
  refine ⟨h, ?_, ?_⟩
  · have h1 := hh 1
    rw [h12.1] at h1
    have h2 := congrArg h h1
    simpa using h2
  · have h1 := hh 2
    rw [h12.2] at h1
    have h2 := congrArg h h1
    simpa using h2

-- Zero is a fixed point of `twoAdicCollatz`, so its image is fixed by `qCollatz 1 1`.
example : ∃ h : ℤ_[2] ≃ PowerSeries (ZMod 2), qCollatz 1 1 (h 0) = h 0 := by
  obtain ⟨h, hh⟩ := qCollatz_conjugate_twoAdicCollatz 1 1 (by simp) (by simp)
  have hT0 : twoAdicCollatz 0 = 0 := by
    have h0 : PadicInt.toZMod (0 : ℤ_[2]) = 0 := map_zero _
    have h2 := two_mul_twoAdicCollatz_of_even h0
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  have h1 := hh 0
  rw [hT0] at h1
  refine ⟨h, ?_⟩
  have h2 := congrArg h h1
  simpa using h2
