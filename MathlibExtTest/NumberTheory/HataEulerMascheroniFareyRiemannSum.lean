/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.HataEulerMascheroniFareyRiemannSum

namespace MetaMathlibExt

-- The smallest admissible partition has one interval and mesh 1/2.
example : |(3 : ℝ) / 2 - ∫ t in (1 / 2 : ℝ)..1, 2 / t| ≤ 1 := by
  let A (k : ℕ) : ℕ := if k = 1 ∨ k = 2 then 1 else 0
  let B (k : ℕ) : ℕ := if k = 1 then 2 else if k = 2 then 1 else 0
  have hindex : Finset.Icc (1 : ℕ) (2 - 1) = {1} := by decide
  have h := abs_sum_farey_partition_sub_integral_le (a := 1) (b := 2) (c := 1) (d := 1)
    (m := 2) (A := A) (B := B) (δ := 1 / 2) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by intro k hk; rw [hindex, Finset.mem_singleton] at hk; subst k; decide)
    (by intro k hk; rw [hindex, Finset.mem_singleton] at hk; subst k; norm_num [B])
  norm_num [hindex, A, B] at h
  exact h

-- Splitting at 2/3 gives two intervals with different widths, 1/6 and 1/3.
example : |(17 : ℝ) / 12 - ∫ t in (1 / 2 : ℝ)..1, 2 / t| ≤ 2 / 3 := by
  let A (k : ℕ) : ℕ := if k = 2 then 2 else if k = 1 ∨ k = 3 then 1 else 0
  let B (k : ℕ) : ℕ := if k = 1 then 2 else if k = 2 then 3 else if k = 3 then 1 else 0
  have hindex : Finset.Icc (1 : ℕ) (3 - 1) = {1, 2} := by decide
  have h := abs_sum_farey_partition_sub_integral_le (a := 1) (b := 2) (c := 1) (d := 1)
    (m := 3) (A := A) (B := B) (δ := 1 / 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by
      intro k hk
      simp only [hindex, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> decide)
    (by
      intro k hk
      simp only [hindex, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> norm_num [B])
  norm_num [hindex, A, B] at h
  exact h

end MetaMathlibExt
