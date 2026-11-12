/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Expected loss decomposition

On a probability space, the expected loss `E[1_D * EAD * LGD]` equals the
probability of the default event `D` times the expected
exposure-times-loss-given-default conditional on `D`. This is a
measure-theoretic identity; it asserts no credit model.

## Main results

* `expectedLoss_eq_defaultProbability_mul_conditionalExpectedLoss`: the
  expected-loss decomposition.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.ExpectedLoss

open MeasureTheory ProbabilityTheory

/-- Expected loss on a probability space: the expected value of the loss
`EAD ω * LGD ω` on the default event `D`, and `0` outside `D`. That is,
`E[L]` for `L = 1_D * EAD * LGD`. -/
noncomputable def expectedLoss {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Set Ω) (EAD LGD : Ω → ℝ) : ℝ :=
  ∫ ω, Set.indicator D (fun ω => EAD ω * LGD ω) ω ∂μ

/-- Probability of the default event `D`. -/
noncomputable def defaultProbability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Set Ω) : ℝ :=
  μ.real D

/-- Expected exposure-times-loss-given-default conditional on default: the
integral of `EAD * LGD` against the conditional measure `μ[|D]`. -/
noncomputable def conditionalExpectedLoss {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Set Ω) (EAD LGD : Ω → ℝ) : ℝ :=
  ∫ ω, EAD ω * LGD ω ∂(ProbabilityTheory.cond μ D)

/-- Expected-loss decomposition (FI16.T03): expected loss equals the probability
of default times the expected exposure-times-loss-given-default conditional on
default. The side condition `μ D ≠ 0` is needed for the conditional measure to
be defined by scaling the restriction; on `μ D = 0` the left side is `0` while
the conditional expectation is not pinned by this statement. -/
theorem expectedLoss_eq_defaultProbability_mul_conditionalExpectedLoss
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {D : Set Ω} (hD : MeasurableSet D) (hμD : μ D ≠ 0)
    {EAD LGD : Ω → ℝ}
    (hInt : IntegrableOn (fun ω => EAD ω * LGD ω) D μ) :
    expectedLoss μ D EAD LGD =
      defaultProbability μ D * conditionalExpectedLoss μ D EAD LGD := by
  unfold expectedLoss defaultProbability conditionalExpectedLoss MeasureTheory.Measure.real
  rw [MeasureTheory.integral_indicator hD]
  have hfin : μ D ≠ ⊤ := measure_ne_top μ D
  have hreal : (μ D).toReal ≠ 0 := by
    simp only [ne_eq, ENNReal.toReal_eq_zero_iff, not_or]
    exact ⟨hμD, hfin⟩
  have hcond : ProbabilityTheory.cond μ D = (μ D)⁻¹ • μ.restrict D := rfl
  rw [hcond, MeasureTheory.integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
  have hscale : (μ D).toReal * ((μ D).toReal)⁻¹ = 1 := mul_inv_cancel₀ hreal
  rw [← mul_assoc, hscale, one_mul]

end MathlibExt.Probability.Finance.ExpectedLoss
