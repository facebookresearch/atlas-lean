/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DiophantineApproximation.ScottishBook152
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for the lattice count in a translated unit disc -/

open MathlibExt.NumberTheory.DiophantineApproximation.ScottishBook152Wanted

-- At the initial center all four axial boundary points count, as does the origin.
example (w : ℝ × ℝ) : DiscLatticeCount w 0 = 5 := by
  let s : Set (ℤ × ℤ) := {(0, 0), (-1, 0), (1, 0), (0, -1), (0, 1)}
  have he : {p : ℤ × ℤ | (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 ≤ 1} = s := by
    ext ⟨a, b⟩
    change (a : ℝ) ^ 2 + (b : ℝ) ^ 2 ≤ 1 ↔ _
    constructor
    · intro h
      have h' : a ^ 2 + b ^ 2 ≤ 1 := by exact_mod_cast h
      have ha : -1 ≤ a ∧ a ≤ 1 := by
        constructor <;> nlinarith [sq_nonneg b, sq_nonneg (a + 1), sq_nonneg (a - 1)]
      have hb : -1 ≤ b ∧ b ≤ 1 := by
        constructor <;> nlinarith [sq_nonneg a, sq_nonneg (b + 1), sq_nonneg (b - 1)]
      obtain ⟨ha₁, ha₂⟩ := ha
      obtain ⟨hb₁, hb₂⟩ := hb
      interval_cases a <;> interval_cases b <;> norm_num [s] at *
    · simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
  simp only [DiscLatticeCount, Nat.cast_zero, zero_mul, sub_zero, he]
  norm_num [s, Set.ncard_insert_of_notMem, Prod.ext_iff]

-- Halfway between adjacent lattice points, only those two points lie in the disc.
example : DiscLatticeCount (1 / 2, 0) 1 = 2 := by
  let s : Set (ℤ × ℤ) := {(0, 0), (1, 0)}
  have he : {p : ℤ × ℤ | ((p.1 : ℝ) - 1 / 2) ^ 2 + (p.2 : ℝ) ^ 2 ≤ 1} = s := by
    ext ⟨a, b⟩
    change ((a : ℝ) - 1 / 2) ^ 2 + (b : ℝ) ^ 2 ≤ 1 ↔ _
    constructor
    · intro h
      have hh : (2 * a - 1) ^ 2 + 4 * b ^ 2 ≤ 4 := by
        exact_mod_cast (show (2 * (a : ℝ) - 1) ^ 2 + 4 * (b : ℝ) ^ 2 ≤ 4 by linarith only [h])
      have ha : 0 ≤ a ∧ a ≤ 1 := by
        constructor <;> nlinarith [sq_nonneg a, sq_nonneg (a - 1), sq_nonneg b]
      obtain ⟨ha₁, ha₂⟩ := ha
      interval_cases a <;> have : b = 0 := by nlinarith [sq_nonneg (b + 1), sq_nonneg (b - 1)]
      all_goals simp [s, this]
    · simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
  simp only [DiscLatticeCount, Nat.cast_one, one_mul, sub_zero, he]
  norm_num [s, Set.ncard_insert_of_notMem]
