/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Rat.Floor
import MathlibExt.NumberTheory.FloorIdentities

open MetaMathlibExt

example (n : ℤ) : ⌊(n : ℝ)⌋ + ⌊-(n : ℝ)⌋ = 0 :=
  floor_add_floor_neg_and_floor_add_eq.1 _ ⟨n, rfl⟩

example : ⌊(-3 / 2 : ℝ)⌋ + ⌊-(-3 / 2 : ℝ)⌋ = -1 := by
  apply floor_add_floor_neg_and_floor_add_eq.2.1
  rintro ⟨n, hn⟩
  have h := congrArg Int.fract hn
  norm_num at h

example : ⌊(-3 / 2 : ℝ) + 1 / 4⌋ = ⌊(-3 / 2 : ℝ)⌋ + ⌊(1 / 4 : ℝ)⌋ := by
  rw [floor_add_floor_neg_and_floor_add_eq.2.2, ite_eq_left (by norm_num)]

example : ⌊(-3 / 2 : ℝ) + 1 / 2⌋ = ⌊(-3 / 2 : ℝ)⌋ + ⌊(1 / 2 : ℝ)⌋ + 1 := by
  rw [floor_add_floor_neg_and_floor_add_eq.2.2, ite_eq_right (by norm_num)]
