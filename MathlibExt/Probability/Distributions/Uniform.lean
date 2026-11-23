/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Moments of a uniform law on a real interval

For `a < b`, a real random variable uniform on `[a, b]` has natural moments
`(b ^ (k + 1) - a ^ (k + 1)) / ((k + 1) * (b - a))`, mean `(a + b) / 2`, and
population variance `(b - a) ^ 2 / 12`.

The underlying measure need not be supplied with a probability instance: this follows from
`IsUniform` and the positive finite length of the interval. The strict endpoint hypothesis
is essential for the probabilistic interpretation; conditioning volume on a singleton is zero.

These proofs use the canonical `IsUniform`/`HasLaw` and interval-integral APIs. They are new
Uniform mathematics, not copied from the archived Gamma donor or a textbook formalization.
-/

@[expose] public section

open Set ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory.pdf.IsUniform

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {a b : ℝ}

private lemma volume_Icc_ne_zero (hab : a < b) : volume (Icc a b) ≠ 0 := by
  rw [Real.volume_Icc]
  exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'

private lemma integrable_pow_of_Icc (hab : a < b) (hu : IsUniform X (Icc a b) P) (k : ℕ) :
    Integrable (fun ω ↦ X ω ^ k) P := by
  have hpow : IntegrableOn (fun x : ℝ ↦ x ^ k) (Icc a b) :=
    (continuous_id.pow k).integrableOn_Icc
  have hcond : Integrable (fun x : ℝ ↦ x ^ k) (ProbabilityTheory.cond volume (Icc a b)) :=
    hpow.smul_measure (ENNReal.inv_ne_top.mpr (volume_Icc_ne_zero hab))
  exact HasLaw.integrable_comp (f := fun x : ℝ ↦ x ^ k) hu hcond

/-- Natural moments of a real random variable uniform on the nondegenerate interval `[a, b]`. -/
theorem integral_pow_of_Icc (hab : a < b) (hu : IsUniform X (Icc a b) P) (k : ℕ) :
    ∫ ω, X ω ^ k ∂P = (b ^ (k + 1) - a ^ (k + 1)) / ((k + 1) * (b - a)) := by
  calc
    ∫ ω, X ω ^ k ∂P = ∫ x, x ^ k ∂ProbabilityTheory.cond volume (Icc a b) :=
      HasLaw.integral_comp (f := fun x : ℝ ↦ x ^ k) hu (by fun_prop)
    _ = (b - a)⁻¹ * ((b ^ (k + 1) - a ^ (k + 1)) / (k + 1)) := by
      rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, Real.volume_Icc,
        ENNReal.toReal_inv, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le),
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le,
        integral_pow]
    _ = (b ^ (k + 1) - a ^ (k + 1)) / ((k + 1) * (b - a)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The mean of a real random variable uniform on `[a, b]` is its midpoint. -/
theorem integral_of_Icc (hab : a < b) (hu : IsUniform X (Icc a b) P) :
    ∫ ω, X ω ∂P = (a + b) / 2 := by
  have hm := integral_pow_of_Icc hab hu 1
  norm_num at hm
  rw [hm]
  field_simp [(sub_pos.mpr hab).ne']
  ring

/-- The population variance of a real random variable uniform on `[a, b]`. -/
theorem variance_of_Icc (hab : a < b) (hu : IsUniform X (Icc a b) P) :
    Var[X; P] = (b - a) ^ 2 / 12 := by
  let : IsProbabilityMeasure P := hu.isProbabilityMeasure (volume_Icc_ne_zero hab)
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top.ne)
  have hX : MemLp X 2 P :=
    (memLp_two_iff_integrable_sq hu.aemeasurable.aestronglyMeasurable).mpr
      (integrable_pow_of_Icc hab hu 2)
  rw [variance_eq_sub hX]
  change (∫ ω, X ω ^ 2 ∂P) - (∫ ω, X ω ∂P) ^ 2 = _
  rw [integral_pow_of_Icc hab hu 2, integral_of_Icc hab hu]
  norm_num
  field_simp [(sub_pos.mpr hab).ne']
  ring

end MeasureTheory.pdf.IsUniform
