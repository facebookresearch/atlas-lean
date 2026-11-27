/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.RieszBrothers
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-! # Tests for the F. and M. Riesz theorem -/

open MeasureTheory
open MathlibExt.Analysis.RieszBrothersWanted.Analysis

namespace MathlibExtTest.Analysis.RieszBrothers

-- Any measure satisfying the hypothesis has no atoms.
example (μ : ComplexMeasure UnitAddCircle)
    (hμ : ∀ n : ℕ, 1 ≤ n → ∫ᵛ z, fourier n z ∂[ContinuousLinearMap.mul ℝ ℂ; μ] = 0)
    (x : UnitAddCircle) : μ {x} = 0 := by
  apply riesz_brothers_theorem μ (hμ := hμ)
  rw [Measure.toENNRealVectorMeasure_apply_measurable (measurableSet_singleton x)]
  exact measure_singleton x

-- Haar measure, regarded as a complex measure, satisfies the hypothesis and has mass one.
private noncomputable def complexHaar : ComplexMeasure UnitAddCircle :=
  AddCircle.haarAddCircle.withDensityᵥ (fun _ : UnitAddCircle ↦ (1 : ℂ))

private lemma integral_complexHaar (f : UnitAddCircle → ℂ) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; complexHaar] =
      ∫ x, f x ∂AddCircle.haarAddCircle := by
  have hv : complexHaar.variation = AddCircle.haarAddCircle := by
    rw [complexHaar, Measure.variation_withDensityᵥ (integrable_const (1 : ℂ))]
    simp
  simp only [VectorMeasure.integral_eq_setToFun, MeasureTheory.integral_eq_setToFun, hv]
  apply setToFun_congr_left'
  intro s hs _
  ext z
  simp [complexHaar, VectorMeasure.transpose, VectorMeasure.mapRange_apply, weightedSMul,
    withDensityᵥ_apply (integrable_const (1 : ℂ)) hs, Complex.real_smul, mul_comm]

example : complexHaar Set.univ = 1 ∧
    complexHaar ≪ᵥ AddCircle.haarAddCircle.toENNRealVectorMeasure := by
  constructor
  · simp [complexHaar, withDensityᵥ_apply (integrable_const (1 : ℂ)) MeasurableSet.univ]
  · apply riesz_brothers_theorem
    intro n hn
    rw [integral_complexHaar]
    exact integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index (by exact_mod_cast (Nat.ne_zero_of_lt hn)) (by norm_num))

-- The point mass at the origin fails the moment hypothesis already at frequency one.
example : ∫ᵛ z, fourier (1 : ℤ) z ∂[ContinuousLinearMap.mul ℝ ℂ;
    VectorMeasure.dirac (0 : UnitAddCircle) (1 : ℂ)] = 1 := by
  simp

end MathlibExtTest.Analysis.RieszBrothers
