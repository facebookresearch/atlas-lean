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
