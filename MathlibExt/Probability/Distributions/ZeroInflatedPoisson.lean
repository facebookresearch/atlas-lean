/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.UnitInterval
public import MathlibExt.Probability.Statistics.PoissonLikelihood

/-!
# Zero-inflated Poisson distribution

A zero-inflated Poisson law mixes a point mass at zero with a Poisson law. The mixing
probability is the probability of a structural zero, not the total probability of observing
zero: the Poisson component can also produce zero.
-/

@[expose] public section

set_option autoImplicit false

namespace ProbabilityTheory

open MeasureTheory Real
open MathlibExt.Probability.Statistics.PoissonLikelihood (poissonLik)
open scoped ENNReal NNReal unitInterval

/-- A zero-inflated Poisson law: return zero with probability `p` and otherwise draw from
`poissonMeasure μ`. The Poisson component can itself produce zeros. -/
noncomputable def zipMeasure (p : I) (μ : ℝ≥0) : Measure ℕ :=
  ENNReal.ofReal (p : ℝ) • Measure.dirac 0 + ENNReal.ofReal (1 - (p : ℝ)) • poissonMeasure μ

instance (p : I) (μ : ℝ≥0) : IsProbabilityMeasure (zipMeasure p μ) := by
  constructor
  simp only [zipMeasure, add_apply, smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_add p.property.1 (sub_nonneg.mpr p.property.2), add_sub_cancel,
    ENNReal.ofReal_one]

/-- The probability of an observed count, with the structural term present only at zero. -/
theorem zipMeasure_real_singleton (p : I) (μ : ℝ≥0) (k : ℕ) :
    (zipMeasure p μ).real {k} = (if k = 0 then (p : ℝ) else 0) +
      (1 - (p : ℝ)) * poissonLik μ k := by
  have h₁ : (ENNReal.ofReal (p : ℝ) • Measure.dirac (0 : ℕ)) {k} ≠ ∞ := by
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have h₂ : (ENNReal.ofReal (1 - (p : ℝ)) • poissonMeasure μ) {k} ≠ ∞ := by
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  rw [zipMeasure, measureReal_add_apply h₁ h₂, measureReal_ennreal_smul_apply,
    measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal p.property.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr p.property.2), poissonMeasure_real_singleton]
  cases k <;> simp [poissonLik, measureReal_def]

/-- The probability of observing zero includes both the structural and sampling zeros. -/
theorem zipMeasure_real_zero (p : I) (μ : ℝ≥0) :
    (zipMeasure p μ).real {0} = (p : ℝ) + (1 - (p : ℝ)) * exp (-(μ : ℝ)) := by
  simp [zipMeasure_real_singleton, poissonLik]

end ProbabilityTheory
