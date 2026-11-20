/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.CircleIntegralResidues

@[expose] public section

open Metric Filter
open scoped Topology

-- Consumer with the original binders.
example {R : ℝ} {z₀ : ℂ} (hR : 0 < R) (h c : ℂ → ℂ) (Z : Finset ℂ)
    (hZ : ∀ a ∈ Z, a ∈ Metric.ball z₀ R)
    (hh : ∀ z ∈ Metric.closedBall z₀ R, z ∉ Z → AnalyticAt ℂ h z)
    (hloc : ∀ a ∈ Z, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, h z = c a / (z - a) + g z) :
    (∮ z in C(z₀, R), h z) = 2 * Real.pi * Complex.I * ∑ a ∈ Z, c a :=
  Complex.circleIntegral_eq_sum_residue_of_simplePole hR h c Z hZ hh hloc

-- One simple pole at the centre: the integral of `z ↦ 3 / z` over the unit
-- circle is `2πi * 3`.
example : (∮ z in C((0 : ℂ), 1), (3 : ℂ) / z) = 2 * Real.pi * Complex.I * 3 := by
  have h := Complex.circleIntegral_eq_sum_residue_of_simplePole (R := 1) (z₀ := 0)
    (h := fun z => (3 : ℂ) / z) (c := fun _ => 3) (Z := {0}) one_pos
    (by simp) (by
      intro z _ hz
      simp only [Finset.mem_singleton] at hz
      exact analyticAt_const.div analyticAt_id (by simpa using hz))
    (by
      intro a ha
      simp only [Finset.mem_singleton] at ha
      refine ⟨fun _ => 0, analyticAt_const, ?_⟩
      filter_upwards with z
      rw [ha]
      simp)
  simpa using h

-- The hypothesis that the pole set lies inside the disc cannot be dropped:
-- `z ↦ z⁻¹` has its pole at the centre, and its unit circle integral is
-- `2πi ≠ 0`, not the empty sum.
example : (∮ z in C((0 : ℂ), 1), z⁻¹) ≠ 0 := by
  have h : (∮ z in C((0 : ℂ), 1), z⁻¹) = 2 * Real.pi * Complex.I := by
    rw [circleIntegral.integral_congr (R := 1) (c := (0 : ℂ))
      (f := fun z : ℂ => z⁻¹) (g := fun z : ℂ => (z - 0)⁻¹) zero_le_one
      (fun z _ => by simp)]
    exact circleIntegral.integral_sub_inv_of_mem_ball (by simp)
  rw [h]
  exact mul_ne_zero (mul_ne_zero two_ne_zero
    (by exact_mod_cast Real.pi_ne_zero : (Real.pi : ℂ) ≠ 0)) Complex.I_ne_zero
