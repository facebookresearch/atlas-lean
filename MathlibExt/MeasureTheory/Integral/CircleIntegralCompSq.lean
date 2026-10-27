/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Circle integrals of functions of `z²`

For every `f : ℂ → ℂ`, `∮_{|z| = R} f(z²) dz = 0` (`circleIntegral_comp_sq_eq_zero`). Since
`circleMap 0 R (θ + π) = -circleMap 0 R θ`, the integrand `θ ↦ (circleMap 0 R)′(θ) f((circleMap 0 R
θ)²)` changes sign under `θ ↦ θ + π`, so the integrals over `[0, π]` and `[π, 2π]` cancel; if the
integrand is not integrable both sides are `0` by convention. The book states this for rational
`f` (Lecture 8); the test file derives that case.

Code-derived port of `circleIntegral_comp_sq_eq_zero` from
`v1/Atlas/ComplexVariables/code/Lecture8.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`, lines 43–92. The archived formalization and its
original license/provenance remain in `v1/` (the original license text is `v1/LICENSE`).
-/

set_option autoImplicit false

open Complex MeasureTheory intervalIntegral Set Function Real

private lemma circleMap_zero_add_pi (R θ : ℝ) :
    circleMap 0 R (θ + π) = -circleMap 0 R θ := by
  simp only [circleMap_zero, ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- For every `f : ℂ → ℂ`, `∮_{|z| = R} f(z²) dz = 0`: the integrand is antiperiodic in the angle,
with antiperiod `π`. -/
public theorem circleIntegral_comp_sq_eq_zero (f : ℂ → ℂ) (R : ℝ) :
    (∮ z in C(0, R), f (z ^ 2)) = 0 := by
  simp only [circleIntegral]
  set g : ℝ → ℂ := fun θ => deriv (circleMap 0 R) θ • f ((circleMap 0 R θ) ^ 2)
  have hanti : ∀ θ, g (θ + π) = -g θ := by
    intro θ
    change deriv (circleMap 0 R) (θ + π) • f ((circleMap 0 R (θ + π)) ^ 2) =
      -(deriv (circleMap 0 R) θ • f ((circleMap 0 R θ) ^ 2))
    rw [deriv_circleMap, deriv_circleMap, circleMap_zero_add_pi]
    simp only [smul_eq_mul, neg_pow_two]
    ring
  have h2pi : (2 : ℝ) * π = π + π := by ring
  rw [h2pi]
  by_cases hint : IntervalIntegrable g volume 0 (π + π)
  · have hpi_pos : (0 : ℝ) ≤ π := le_of_lt pi_pos
    have hint1 : IntervalIntegrable g volume 0 π := by
      apply hint.mono_set
      rw [uIcc_of_le hpi_pos, uIcc_of_le (by linarith)]
      exact Icc_subset_Icc_right (by linarith)
    have hint2 : IntervalIntegrable g volume π (π + π) := by
      apply hint.mono_set
      rw [uIcc_of_le (by linarith : π ≤ π + π), uIcc_of_le (by linarith)]
      exact Icc_subset_Icc_left hpi_pos
    rw [← integral_add_adjacent_intervals hint1 hint2]
    have hsub : ∫ x in π..(π + π), g x = ∫ x in (0 : ℝ)..π, g (x + π) := by
      rw [integral_comp_add_right]
      simp only [zero_add]
    rw [hsub]
    have hcongr : (∫ θ in (0 : ℝ)..π, g (θ + π)) = -(∫ θ in (0 : ℝ)..π, g θ) := by
      rw [show (fun θ => g (θ + π)) = fun θ => -g θ from funext (fun θ => hanti θ)]
      exact intervalIntegral.integral_neg
    rw [hcongr]
    simp
  · exact integral_undef hint
