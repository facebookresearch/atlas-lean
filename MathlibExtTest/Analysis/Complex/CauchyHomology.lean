/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import MathlibExt.Analysis.Complex.CauchyHomology

set_option autoImplicit false

open Complex Metric Set

theorem zero_notMem_range_circlePath : (0 : ℂ) ∉ range (circlePath 0 1) := fun h => by
  have := range_circlePath_subset 0 1 h
  simp at this

-- The unit circle is homologous to zero in `ℂ` ...
theorem isHomologousToZero_circlePath_univ : IsHomologousToZero (circlePath 0 1) univ :=
  ⟨subset_univ _, fun a ha => absurd (mem_univ a) ha⟩

-- ... but not in `ℂ \ {0}`, where it winds once around the missing point.
example : ¬IsHomologousToZero (circlePath 0 1) {0}ᶜ := fun h => by
  have h0 := h.2 0 (by simp)
  rw [windingNumber_circlePath_of_mem_ball (mem_ball_self one_pos)] at h0
  exact one_ne_zero h0

-- Cauchy's theorem for a polynomial over the unit circle.
example : ∫ᶜ z in circlePath 0 1, (z ^ 2 + 3 * z + 1) • ContinuousLinearMap.id ℂ ℂ = 0 :=
  (curveIntegral_eq_zero_of_differentiableOn isOpen_univ (f := fun z => z ^ 2 + 3 * z + 1)
    (by fun_prop)).1 _ (isPiecewiseC1_circlePath 0 1) isHomologousToZero_circlePath_univ

-- The simply connected clause: the complement of `ℂ` in `OnePoint ℂ` is `{∞}`, so every closed
-- piecewise `C¹` path in `ℂ` integrates `exp` to zero.
example : ∫ᶜ z in circlePath 0 1, exp z • ContinuousLinearMap.id ℂ ℂ = 0 := by
  refine (curveIntegral_eq_zero_of_differentiableOn isOpen_univ
    differentiable_exp.differentiableOn).2 ?_ _ (isPiecewiseC1_circlePath 0 1) (subset_univ _)
  rw [image_univ, OnePoint.compl_range_coe]
  exact isConnected_singleton

-- Cauchy's integral formula at the centre of the unit circle: `(2πi)⁻¹ ∫ exp ζ / ζ dζ = exp 0`.
example : (2 * Real.pi * I)⁻¹ *
    ∫ᶜ ζ in circlePath 0 1, (exp ζ / (ζ - 0)) • ContinuousLinearMap.id ℂ ℂ = 1 := by
  rw [← windingNumber_mul_eq_two_pi_I_inv_mul_curveIntegral isOpen_univ
    differentiable_exp.differentiableOn (isPiecewiseC1_circlePath 0 1)
    isHomologousToZero_circlePath_univ zero_notMem_range_circlePath,
    windingNumber_circlePath_of_mem_ball (mem_ball_self one_pos), exp_zero, one_mul]

-- Claims 2 and 3 for `exp` and the unit circle: `h ≡ 0` on `ℂ`.
example (z : ℂ) :
    (2 * Real.pi * I)⁻¹ * ∫ᶜ ζ in circlePath 0 1, dslope exp z ζ • ContinuousLinearMap.id ℂ ℂ =
      0 :=
  (curveIntegral_dslope_eq_zero_and_cauchy_integral_formula isOpen_univ
    differentiable_exp.differentiableOn (isPiecewiseC1_circlePath 0 1)
    isHomologousToZero_circlePath_univ).1 z (mem_univ z)

example : ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ ∀ z ∈ univ,
    h z = (2 * Real.pi * I)⁻¹ *
      ∫ᶜ ζ in circlePath 0 1, dslope exp z ζ • ContinuousLinearMap.id ℂ ℂ := by
  obtain ⟨-, h, hd, hΩ, -⟩ := exists_differentiable_of_isHomologousToZero isOpen_univ
    differentiable_exp.differentiableOn (isPiecewiseC1_circlePath 0 1)
    isHomologousToZero_circlePath_univ
  exact ⟨h, hd, hΩ⟩

-- Cauchy's theorem for a cycle: `C(0, 2) - C(0, 1)` is homologous to zero in `ℂ \ {0}`, so
-- `∫_{C(0, 2)} z⁻¹ dz = ∫_{C(0, 1)} z⁻¹ dz`.
example : ∑ b : Bool, ((if b then 1 else -1 : ℤ) : ℂ) *
    ∫ᶜ z in circlePath 0 (if b then 2 else 1), z⁻¹ • ContinuousLinearMap.id ℂ ℂ = 0 := by
  refine sum_curveIntegral_eq_zero (γ := fun b : Bool => circlePath 0 (if b then 2 else 1))
    (fun _ => isPiecewiseC1_circlePath _ _) (fun b : Bool => if b then 1 else -1)
    isOpen_compl_singleton (fun b => ?_) (fun a ha => ?_)
    fun z hz => (differentiableAt_inv hz).differentiableWithinAt
  · intro w hw hw0
    rw [mem_singleton_iff] at hw0
    have := range_circlePath_subset 0 _ hw
    subst hw0
    cases b <;> simp at this
  · rw [mem_compl_singleton_iff, not_not] at ha
    subst ha
    simp [windingNumber_circlePath_of_mem_ball]

#print axioms IsHomologousToZero
#print axioms sum_curveIntegral_eq_zero
#print axioms isHomologousToZero_of_isPreconnected
#print axioms curveIntegral_eq_zero_of_differentiableOn
#print axioms windingNumber_mul_eq_two_pi_I_inv_mul_curveIntegral
#print axioms exists_differentiable_of_isHomologousToZero
#print axioms curveIntegral_dslope_eq_zero_and_cauchy_integral_formula
