/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SierpinskiRieselRepdigitsInfiniteSierpinskiRepdigits

/-! # Tests for `MathlibExt.NumberTheory.SierpinskiRieselRepdigitsInfiniteSierpinskiRepdigits` -/

namespace MathlibExtTest.NumberTheory.SierpinskiRieselRepdigitsInfiniteSierpinskiRepdigits

open MetaMathlibExt

-- The least base above 78557 already has a Sierpiński repdigit.
example : ∃ N k t : ℕ, 1 ≤ k ∧ k < 78558 ∧ 1 ≤ t ∧
    N = repstring 78558 k 0 t ∧ IsSierpinskiNumber N := by
  have hinf := infinite_sierpinski_repdigits (b := 78558) (by decide)
  obtain ⟨N, hN⟩ := hinf.nonempty
  exact ⟨N, hN⟩

-- Any such repdigit gives a concrete composite of the form `N * 2 + 1`.
example : ∃ N k t : ℕ, 1 ≤ k ∧ k < 78558 ∧ 1 ≤ t ∧
    N = repstring 78558 k 0 t ∧ ¬ (N * 2 + 1).Prime := by
  have hinf := infinite_sierpinski_repdigits (b := 78558) (by decide)
  obtain ⟨N, hN⟩ := hinf.nonempty
  obtain ⟨k, t, hk1, hkb, ht1, hNeq, hS⟩ := hN
  refine ⟨N, k, t, hk1, hkb, ht1, hNeq, ?_⟩
  simpa only [pow_one] using hS.2 1 le_rfl

end MathlibExtTest.NumberTheory.SierpinskiRieselRepdigitsInfiniteSierpinskiRepdigits
