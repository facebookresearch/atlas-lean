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
# Expected loss factorization: PD x LGD x EAD

When exposure at default is constant on the default event, expected loss
factors as PD times the conditional expectation of LGD times EAD; when LGD is
also constant on the default event, expected loss reduces to PD x LGD x EAD.
The interface definitions are a local copy of the FI16.T03 interface (a
concurrent gap, not on main at the time of writing); future unification with
`MathlibExt.Probability.Finance.ExpectedLoss` is intended.

## Main results

* `expectedLoss_eq_defaultProbability_mul_condExpectedLGD_mul_ead`: the
  factorization step with EAD constant on the default event.
* `expectedLoss_eq_pd_mul_lgd_mul_ead`: the PD x LGD x EAD formula.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.ExpectedLossFactorization

open MeasureTheory ProbabilityTheory

/-- Expected loss: the expected value of `EAD ω * LGD ω` on the default event
`D`, and `0` outside `D`. Local copy of the FI16.T03 interface (FI16.T03 is a
concurrent gap in this run, not on main); future unification with
`MathlibExt.Probability.Finance.ExpectedLoss` is noted in the PR body. -/
noncomputable def expectedLoss {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Set Ω) (EAD LGD : Ω → ℝ) : ℝ :=
  ∫ ω, Set.indicator D (fun ω => EAD ω * LGD ω) ω ∂μ

/-- Probability of the default event `D`. -/
noncomputable def defaultProbability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Set Ω) : ℝ :=
  μ.real D

/-- Factorization step (FI16.T04): when exposure at default is the constant
`ead` on the default event, expected loss factors as PD times the conditional
expectation of LGD times `ead`. This is the separately stated factorization
assumption: EAD constant on `D` (no independence of LGD from anything is used). -/
theorem expectedLoss_eq_defaultProbability_mul_condExpectedLGD_mul_ead
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {D : Set Ω} (hD : MeasurableSet D) (hμD : μ D ≠ 0)
    {EAD LGD : Ω → ℝ} {ead : ℝ} (hEAD : ∀ ω ∈ D, EAD ω = ead)
    (hInt : IntegrableOn (fun ω => EAD ω * LGD ω) D μ)
    (hIntLGD : IntegrableOn LGD D μ) :
    expectedLoss μ D EAD LGD =
      defaultProbability μ D * (∫ ω, LGD ω ∂(ProbabilityTheory.cond μ D)) * ead := by
  unfold expectedLoss defaultProbability
  rw [integral_indicator hD]
  have hEqOn : Set.EqOn (fun ω => EAD ω * LGD ω) (fun ω => ead * LGD ω) D :=
    fun ω hω => congrArg (fun x => x * LGD ω) (hEAD ω hω)
  rw [setIntegral_congr_fun hD hEqOn, integral_const_mul ead LGD]
  have hcond : (∫ ω, LGD ω ∂(ProbabilityTheory.cond μ D))
      = ((μ D)⁻¹).toReal * ∫ ω in D, LGD ω ∂μ := by
    simp only [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul]
  rw [hcond]
  have htop : μ D ≠ ⊤ := measure_ne_top μ D
  have hscale : μ.real D * ((μ D)⁻¹).toReal = 1 := by
    simp only [Measure.real, ← ENNReal.toReal_mul, ENNReal.mul_inv_cancel hμD htop,
      ENNReal.toReal_one]
  calc ead * (∫ ω in D, LGD ω ∂μ)
      = (μ.real D * ((μ D)⁻¹).toReal) * ((∫ ω in D, LGD ω ∂μ) * ead) := by
        rw [hscale, one_mul]; ring
    _ = μ.real D * (((μ D)⁻¹).toReal * (∫ ω in D, LGD ω ∂μ)) * ead := by ring

/-- PD x LGD x EAD (FI16.T04): when exposure at default is the constant `ead`
on `D` and loss-given-default is the constant `lgd` on `D`, expected loss
reduces to PD * LGD * EAD. -/
theorem expectedLoss_eq_pd_mul_lgd_mul_ead
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {D : Set Ω} (hD : MeasurableSet D) (hμD : μ D ≠ 0)
    {EAD LGD : Ω → ℝ} {ead lgd : ℝ} (hEAD : ∀ ω ∈ D, EAD ω = ead)
    (hLGD : ∀ ω ∈ D, LGD ω = lgd)
    (hInt : IntegrableOn (fun ω => EAD ω * LGD ω) D μ)
    (hIntLGD : IntegrableOn LGD D μ) :
    expectedLoss μ D EAD LGD = defaultProbability μ D * lgd * ead := by
  have hstep :=
    expectedLoss_eq_defaultProbability_mul_condExpectedLGD_mul_ead μ hD hμD hEAD hInt hIntLGD
  rw [hstep]
  have hcondLGD : (∫ ω, LGD ω ∂(ProbabilityTheory.cond μ D)) = lgd := by
    have htop : μ D ≠ ⊤ := measure_ne_top μ D
    have hcinv : (μ D)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr htop
    have hmem : ∀ᵐ ω ∂(ProbabilityTheory.cond μ D), ω ∈ D := by
      simp only [ProbabilityTheory.cond, Measure.ae_ennreal_smul_measure_iff hcinv]
      exact ae_restrict_mem hD
    have heq : LGD =ᵐ[ProbabilityTheory.cond μ D] fun _ => lgd :=
      hmem.mono fun ω hω => hLGD ω hω
    have _hcondProb := ProbabilityTheory.cond_isProbabilityMeasure (μ := μ) (s := D) hμD
    calc (∫ ω, LGD ω ∂(ProbabilityTheory.cond μ D))
        = ∫ ω, lgd ∂(ProbabilityTheory.cond μ D) := integral_congr_ae heq
      _ = lgd := by
          rw [integral_const]
          have h1 : (ProbabilityTheory.cond μ D).real Set.univ = 1 := by
            simp only [Measure.real, IsProbabilityMeasure.measure_univ,
              ENNReal.toReal_one]
          rw [h1, one_smul]
  rw [hcondLGD]

end MathlibExt.Probability.Finance.ExpectedLossFactorization
