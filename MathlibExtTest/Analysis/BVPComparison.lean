/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.BVPComparison
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Tests for the Dirichlet comparison principle -/

open Set MathlibExt.Analysis.BVPComparisonWanted.Analysis.ODE

-- The parabola meets its chord at both endpoints and has strictly larger second derivative.
example : ∀ x ∈ Icc (0 : ℝ) 1, x ^ 2 ≤ x := by
  have hsquare : deriv (fun y : ℝ ↦ y ^ 2) = fun y ↦ 2 * y := by
    funext y
    simp
  apply bvp_comparison univ isOpen_univ (subset_univ _) (fun y ↦ y ^ 2) id
  · exact fun x _ ↦ (hasDerivAt_pow 2 x).differentiableAt.hasDerivAt
  · intro x _
    rw [hsquare]
    exact (differentiableAt_fun_id.const_mul 2).hasDerivAt
  · exact fun _ _ ↦ differentiableAt_id.hasDerivAt
  · simp [hasDerivAt_const]
  · simp [hsquare, deriv_const_mul_id]
  · simp
  · simp

-- Equal second derivatives also suffice when only the right endpoint values coincide.
example : ∀ x ∈ Icc (0 : ℝ) 1, x ≤ 1 := by
  apply bvp_comparison univ isOpen_univ (subset_univ _) id (fun _ ↦ 1) <;>
    simp [hasDerivAt_id, hasDerivAt_const]
