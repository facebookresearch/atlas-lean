/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.RouthHurwitzCubic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- (z + 1)(z² + z + 1) is strictly stable, including its nonreal pair.
example : ∀ z : ℂ, z ^ 3 + 2 * z ^ 2 + 2 * z + 1 = 0 → z.re < 0 := by
  simpa using (routhHurwitzCubic_iff 1 2 2).mpr (by norm_num)

-- At a₂ * a₁ = a₀, the conjugate pair ±I lies on the imaginary axis.
private theorem root_at_hurwitz_boundary (z : ℂ) (hz : z ^ 2 = -1) :
    z ^ 3 + z ^ 2 + z + 1 = 0 := by
  linear_combination (z + 1) * hz

example : ∀ z ∈ ({Complex.I, -Complex.I} : Set ℂ),
    z ^ 3 + z ^ 2 + z + 1 = 0 ∧ z.re = 0 := by
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact ⟨root_at_hurwitz_boundary _ Complex.I_sq, by simp⟩
  · exact ⟨root_at_hurwitz_boundary _ (by simp [Complex.I_sq]), by simp⟩

example : ¬ (∀ z : ℂ, z ^ 3 + z ^ 2 + z + 1 = 0 → z.re < 0) := by
  intro h
  have h' := (routhHurwitzCubic_iff 1 1 1).mp (by simpa using h)
  norm_num at h'

-- At a₀ = 0, the product inequality is strict, but zero is a root.
example : ∃ z : ℂ, z ^ 3 + z ^ 2 + 2 * z = 0 ∧ z.re = 0 := ⟨0, by simp, by simp⟩

example : ¬ (∀ z : ℂ, z ^ 3 + z ^ 2 + 2 * z = 0 → z.re < 0) := by
  intro h
  have h' := (routhHurwitzCubic_iff 0 2 1).mp (by simpa using h)
  norm_num at h'

end MetaMathlibExt
