/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Calculus.EulerMaclaurinFormula

import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Analysis.Calculus.EulerMaclaurinFormula

open MetaMathlibExt

-- At an integer the kernel is the Bernoulli number, here `B₂ = 1 / 6`.
example : bernoulliKernel 2 (-3 : ℤ) = 1 / 6 := by
  rw [bernoulliKernel_intCast, bernoulli_two]
  norm_num

-- Odd kernels of degree at least three vanish at every integer.
example : bernoulliKernel 3 (5 : ℤ) = 0 := by
  rw [bernoulliKernel_intCast, bernoulli_eq_zero_of_odd (by decide) (by norm_num)]
  simp

-- The kernel reads only the fractional part: `B₁(fract (7 / 2)) = 1 / 2 - 1 / 2`.
example : bernoulliKernel 1 (7 / 2) = 0 := by
  have hfract : Int.fract (7 / 2 : ℝ) = 1 / 2 :=
    Int.fract_eq_iff.mpr ⟨by norm_num, by norm_num, 3, by norm_num⟩
  rw [bernoulliKernel_apply, hfract, bernoulliFun_one]
  norm_num

-- Shifting by a whole number of periods leaves the kernel unchanged.
example (p : ℕ) (x : ℝ) : bernoulliKernel p (x + 3) = bernoulliKernel p x := by
  simpa using (bernoulliKernel_periodic p).nat_mul 3 x

-- Away from degree one the kernel is continuous, and odd kernels from degree three are bounded.
example : Continuous (bernoulliKernel 2) :=
  bernoulliKernel_continuous (by norm_num)

example : ∃ C : ℝ, ∀ x : ℝ, ‖bernoulliKernel 3 x‖ ≤ C :=
  bernoulliKernel_norm_le 1 (by norm_num)

-- On `[0, 1)` the degree-two kernel is the Bernoulli polynomial `x ^ 2 - x + 1 / 6`.
example : ∀ x ∈ Set.Ico (0 : ℝ) 1, bernoulliKernel 2 x = x ^ 2 - x + 1 / 6 := by
  intro x hx
  rw [bernoulliKernel_apply, Int.fract_eq_self.mpr hx]
  simp [bernoulliFun, Polynomial.bernoulli, Finset.sum_range_succ, bernoulli_two]
  ring

end MathlibExtTest.Analysis.Calculus.EulerMaclaurinFormula
