/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import MathlibExt.Analysis.Complex.TaylorRemainder

set_option autoImplicit false

open Complex Metric
open scoped Real

-- With `n = 0` the remainder is `f` itself, and the integral clause is Cauchy's formula.
example {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    exp z = (2 * π * I)⁻¹ * ∮ ζ in C(0, 1), exp ζ / (ζ - z) := by
  obtain ⟨g, -, hexp, hint⟩ :=
    exists_taylor_remainder_circleIntegral isOpen_univ (Set.mem_univ 0) analyticOnNhd_cexp 0
  have h0 := hexp z (Set.mem_univ z)
  have h1 := hint 1 (Set.subset_univ _) z hz
  simp only [Finset.range_zero, Finset.sum_empty, pow_zero, mul_one, one_mul, zero_add] at h0 h1
  rw [h0, h1]

-- The coefficients are the Taylor coefficients: `exp z = 1 + z + g z * z ^ 2` with `g` entire.
example : ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g Set.univ ∧ ∀ z, exp z = 1 + z + g z * z ^ 2 := by
  obtain ⟨g, hg, hexp, -⟩ :=
    exists_taylor_remainder_circleIntegral isOpen_univ (Set.mem_univ 0) analyticOnNhd_cexp 2
  refine ⟨g, hg, fun z ↦ ?_⟩
  simpa [Finset.sum_range_succ] using hexp z (Set.mem_univ z)

-- A proper open set: `(1 - z)⁻¹` on the unit disc, with the integral over `|ζ| = 1 / 2`.
example (n : ℕ) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 1) ∧ ∀ z ∈ ball (0 : ℂ) (1 / 2),
      g z = (2 * π * I)⁻¹ * ∮ ζ in C(0, 1 / 2), (1 - ζ)⁻¹ / (ζ ^ n * (ζ - z)) := by
  have hf : AnalyticOnNhd ℂ (fun z : ℂ ↦ (1 - z)⁻¹) (ball 0 1) := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_ball
    refine ((differentiableOn_const 1).sub differentiableOn_id).inv fun z hz h ↦ ?_
    rw [sub_eq_zero] at h
    subst h
    simp at hz
  obtain ⟨g, hg, -, hint⟩ :=
    exists_taylor_remainder_circleIntegral isOpen_ball (mem_ball_self one_pos) hf n
  refine ⟨g, hg, fun z hz ↦ ?_⟩
  simpa only [sub_zero] using hint (1 / 2) (closedBall_subset_ball (by norm_num)) z hz

#print axioms Complex.exists_taylor_remainder_circleIntegral
