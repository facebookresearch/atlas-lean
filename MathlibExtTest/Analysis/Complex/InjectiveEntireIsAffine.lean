/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.InjectiveEntireIsAffine
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open MathlibExt.Analysis.Complex.InjectiveEntireIsAffineWanted

-- In the affine case the slope and intercept recovered by the classification are unique.
example : ∃ a b : ℂ, a ≠ 0 ∧ (∀ z : ℂ, 2 * z + 3 = a * z + b) ∧ a = 2 ∧ b = 3 := by
  have hdiff : Differentiable ℂ (fun z : ℂ => 2 * z + 3) := by fun_prop
  have hinj : Function.Injective (fun z : ℂ => 2 * z + 3) := by
    intro x y h
    have hxy : (2 : ℂ) * x = 2 * y := add_right_cancel h
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hxy
  obtain ⟨a, b, ha0, heq⟩ := exists_affine_of_differentiable_injective _ hdiff hinj
  have hb : b = 3 := by simpa using (heq 0).symm
  have h := heq 1
  simp only [mul_one, hb] at h
  exact ⟨a, b, ha0, heq, (add_right_cancel h).symm, hb⟩
