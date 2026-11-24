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
-- `z ↦ (z - 2)⁻¹` has its pole at `2`, outside the unit disc, so its unit
-- circle integral is `0`, not `2πi` times the residue at `2`.
example : (∮ z in C((0 : ℂ), 1), (z - 2)⁻¹) ≠
    2 * Real.pi * Complex.I * ∑ a ∈ ({2} : Finset ℂ), (1 : ℂ) := by
  have h0 : (∮ z in C((0 : ℂ), 1), (z - 2)⁻¹) = 0 := by
    have h := Complex.circleIntegral_eq_sum_residue_of_simplePole (R := 1) (z₀ := 0)
      one_pos (fun z => (z - 2)⁻¹) (fun _ => 1) ∅ (by simp)
      (by
        intro z hz _
        refine (analyticAt_id.sub analyticAt_const).inv ?_
        intro hzero
        have hz2 : z = 2 := sub_eq_zero.mp hzero
        rw [hz2] at hz
        norm_num [Metric.mem_closedBall] at hz)
      (by simp)
    simpa using h
  rw [h0, Finset.sum_singleton, mul_one]
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero
      (by exact_mod_cast Real.pi_ne_zero : (Real.pi : ℂ) ≠ 0)) Complex.I_ne_zero
  exact Ne.symm hne
