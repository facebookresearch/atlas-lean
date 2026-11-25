/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ClassicalWythoffGrundy

namespace MetaMathlibExt.ClassicalWythoffGrundyTest

example : wythoffPassGrundy 0 0 false = 0 := by
  exact (wythoffGrundy_eq_zero_iff (x := 0) (y := 0)).2 ⟨0, Or.inl (by simp)⟩

-- The first positive Beatty pair is a P-position in either orientation.
example : wythoffPassGrundy 1 2 false = 0 ∧ wythoffPassGrundy 2 1 false = 0 := by
  have h : ⌊((1 : ℕ) : ℝ) * Real.goldenRatio⌋₊ = 1 := by
    rw [Nat.cast_one, one_mul, Nat.floor_eq_iff Real.goldenRatio_pos.le]
    norm_num
    exact ⟨Real.one_lt_goldenRatio.le, Real.goldenRatio_lt_two⟩
  exact ⟨(wythoffGrundy_eq_zero_iff 1 2).2 ⟨1, Or.inl ⟨h.symm, by rw [h]⟩⟩,
    (wythoffGrundy_eq_zero_iff 2 1).2 ⟨1, Or.inr ⟨by rw [h], h.symm⟩⟩⟩

-- On the diagonal only the origin is a P-position.
example : wythoffPassGrundy 1 1 false ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (wythoffGrundy_eq_zero_iff 1 1).1 h
  have hn0 : n = 0 := by rcases hn with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega
  subst n
  simp at hn

end MetaMathlibExt.ClassicalWythoffGrundyTest
