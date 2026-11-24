/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.InfiniteWord.GutkovskiyFloor

open MetaMathlibExt

-- The representation 0 of zero uses the even branch.
example : ⌊(√3 - 1) / 2 * (0 : ℝ) + √3 / 3⌋ = 0 := by
  have h := (gutkovskiy_eq_two_mul_floor (n := 0) (a := [0])
    (by decide) (by decide) rfl).2 (Or.inl rfl)
  rw [gutkovskiy_initial.1] at h
  norm_num1 at h
  omega

-- In most-significant-first order, 021 represents 7. The leading zero is allowed.
example : ⌊(√3 - 1) / 2 * (7 : ℝ)⌋ = 2 := by
  have h := (gutkovskiy_eq_two_mul_floor (n := 7) (a := [1, 2, 0])
    (by decide) (by decide) rfl).1 rfl
  rw [show gutkovskiy 7 = 5 by decide] at h
  norm_num1 at h
  omega

-- The offset changes the floor from zero to one for the single digit 2.
example : ⌊(√3 - 1) / 2 * (2 : ℝ) + √3 / 3⌋ = 1 := by
  have h := (gutkovskiy_eq_two_mul_floor (n := 2) (a := [2])
    (by decide) (by decide) rfl).2 (Or.inr rfl)
  rw [gutkovskiy_initial.2.2.1] at h
  norm_num1 at h
  omega
