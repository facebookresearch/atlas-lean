/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.StrongLaw

/-!
# Classical measurement error and attenuation

Classical additive measurement error, scalar model with intercept:
`W = X + e` is observed, `Y = α + β X + ε` is the latent regression, and
the population OLS slope of `Y` on the mismeasured `W` is the attenuated
value `β * Var X / (Var X + Var e)`. The sample (centered) slope converges
to it almost surely.

The attenuation formula REQUIRES the latent regression to be exogenous:
`X` independent of `ε` (hypothesis `hXε` in both theorems). Without it the
formula is false: with `e = 0` and `ε = X`, the `W`-slope is `β + 1`, not
`β`. The proof also uses `e` independent of `X` and of `ε`.

Reuse: the population proof uses Mathlib covariance algebra
(`covariance_add_left/right`, `covariance_self`, `covariance_eq_sub`,
`variance_eq_sub`); the equivalent packaged OLS identity is Atlas
`LinearMomentModel.covariance_div_variance`. The plim uses the strong law
`ProbabilityTheory.strong_law_ae_real` for the four sample moments.

## Main results

- `measurementError_population_attenuation`: the population attenuated slope.
- `sampleSlopeME`: the centered sample OLS slope of `Y` on `W`.
- `measurementError_plim`: the sample slope converges a.s. to the
  attenuated value.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MathlibExt.Probability.Statistics.MeasurementErrorAttenuation

/-- Centered cross-sum identity, division-free core. -/
private theorem centered_sum_core (w y : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (w i - a) * (y i - b)
    = (∑ i ∈ Finset.range n, w i * y i) - a * (∑ i ∈ Finset.range n, y i)
      - b * (∑ i ∈ Finset.range n, w i) + (n : ℝ) * (a * b) := by
  simp_rw [sub_mul, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have e1 : ∑ i ∈ Finset.range n, a * y i = a * (∑ i ∈ Finset.range n, y i) :=
    (Finset.mul_sum _ _ _).symm
  have e2 : ∑ i ∈ Finset.range n, w i * b = (∑ i ∈ Finset.range n, w i) * b :=
    (Finset.sum_mul _ _ _).symm
  have e3 : ∑ i ∈ Finset.range n, a * b = (n : ℝ) * (a * b) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [e1, e2, e3]
  ring

/-- Centered cross-sum identity with sample means. -/
private theorem centered_sum_div (w y : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range n,
        (w i - (∑ j ∈ Finset.range n, w j) / (n : ℝ)) *
          (y i - (∑ j ∈ Finset.range n, y j) / (n : ℝ))
    = (∑ i ∈ Finset.range n, w i * y i)
      - ((∑ j ∈ Finset.range n, w j) / (n : ℝ)) *
        ((∑ j ∈ Finset.range n, y j) / (n : ℝ)) * (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have h : n ≠ 0 := by omega
    exact_mod_cast h
  have h := centered_sum_core w y ((∑ j ∈ Finset.range n, w j) / (n : ℝ))
    ((∑ j ∈ Finset.range n, y j) / (n : ℝ)) n
  rw [h]
  field_simp
  ring

set_option linter.unusedVariables false in
/-- Population attenuation: the OLS slope of `Y` on the mismeasured `W` equals
`β * Var X / (Var X + Var e)`. Prove it from Mathlib covariance algebra
(`covariance_add_left/right`, `covariance_self`); the equivalent packaged OLS
identity is `LinearMomentModel.covariance_div_variance` in Atlas, cited in
the PR docstring. -/
theorem measurementError_population_attenuation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X e ε : Ω → ℝ} {α β : ℝ}
    (hX : MemLp X 2 μ) (he : MemLp e 2 μ) (hε : MemLp ε 2 μ)
    (hXe : IndepFun X e μ) (hXε : IndepFun X ε μ) (heε : IndepFun e ε μ)
    (hW : variance (fun ω => X ω + e ω) μ ≠ 0) :
    covariance (fun ω => X ω + e ω) (fun ω => α + β * X ω + ε ω) μ /
        variance (fun ω => X ω + e ω) μ =
      β * variance X μ / (variance X μ + variance e μ) := by
  have h1 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hWmem : MemLp (fun ω => X ω + e ω) 2 μ := hX.add he
  have hβX : MemLp (fun ω => β * X ω) 2 μ := hX.const_mul β
  have hβXε : MemLp (fun ω => β * X ω + ε ω) 2 μ := hβX.add hε
  have hβXε_int : Integrable (fun ω => β * X ω + ε ω) μ :=
    hβXε.integrable h1
  have hα : (fun ω => α + β * X ω + ε ω) = fun ω => α + (β * X ω + ε ω) := by
    funext ω; ring
  have hcov0 : covariance (fun ω => X ω + e ω) (fun ω => α + β * X ω + ε ω) μ
      = covariance (fun ω => X ω + e ω) (fun ω => β * X ω + ε ω) μ := by
    rw [hα]
    exact covariance_const_add_right hβXε_int α
  have hcov1 : covariance (fun ω => X ω + e ω) (fun ω => β * X ω + ε ω) μ
      = covariance (fun ω => X ω + e ω) (fun ω => β * X ω) μ
        + covariance (fun ω => X ω + e ω) ε μ :=
    covariance_add_right (X := fun ω => X ω + e ω) (Y := fun ω => β * X ω)
      (Z := ε) hWmem hβX hε
  have hsmuleq : (fun ω => β * X ω) = β • X := by
    funext ω; exact (smul_eq_mul β (X ω)).symm
  have hcov2 : covariance (fun ω => X ω + e ω) (fun ω => β * X ω) μ
      = β * covariance (fun ω => X ω + e ω) X μ := by
    rw [hsmuleq]
    exact covariance_smul_right β
  have hcovWX : covariance (fun ω => X ω + e ω) X μ = variance X μ := by
    have h := covariance_add_left (X := X) (Y := e) (Z := X) hX he hX
    have hself : covariance X X μ = variance X μ :=
      covariance_self hX.aestronglyMeasurable.aemeasurable
    have hzero : covariance e X μ = 0 := hXe.symm.covariance_eq_zero he hX
    rw [hself, hzero, add_zero] at h
    exact h
  have hcovWε : covariance (fun ω => X ω + e ω) ε μ = 0 := by
    have h := covariance_add_left (X := X) (Y := e) (Z := ε) hX he hε
    have hz1 : covariance X ε μ = 0 := hXε.covariance_eq_zero hX hε
    have hz2 : covariance e ε μ = 0 := heε.covariance_eq_zero he hε
    rw [hz1, hz2, add_zero] at h
    exact h
  have hVarW : variance (fun ω => X ω + e ω) μ
      = variance X μ + variance e μ :=
    hXe.variance_add hX he
  have hCov : covariance (fun ω => X ω + e ω) (fun ω => α + β * X ω + ε ω) μ
      = β * variance X μ := by
    rw [hcov0, hcov1, hcov2, hcovWX, hcovWε]
    ring
  rw [hCov, hVarW]

/-- The centered sample OLS slope of `Y` on `W` from the first `n`
observations (intercept included via centering). -/
noncomputable def sampleSlopeME {Ω : Type*} [MeasurableSpace Ω]
    (X e ε : ℕ → Ω → ℝ) (α β : ℝ) (n : ℕ) : Ω → ℝ := fun ω =>
  (∑ i ∈ Finset.range n,
      ((X i ω + e i ω) - (∑ j ∈ Finset.range n, (X j ω + e j ω)) / (n : ℝ)) *
        ((α + β * X i ω + ε i ω) -
          (∑ j ∈ Finset.range n, (α + β * X j ω + ε j ω)) / (n : ℝ))) /
    (∑ i ∈ Finset.range n,
      ((X i ω + e i ω) - (∑ j ∈ Finset.range n, (X j ω + e j ω)) / (n : ℝ)) ^ 2)

/-- Attenuation probability limit: the sample slope converges a.s. to
`β * Var X / (Var X + Var e)`. The triples `(X i, e i, ε i)` are iid across `i`;
the time-`0` independence hypotheses give the population limit value. -/
theorem measurementError_plim {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X e ε : ℕ → Ω → ℝ} {α β : ℝ}
    (hJoint : iIndepFun (fun i ω => (X i ω, e i ω, ε i ω)) μ)
    (hIdent : ∀ i, IdentDistrib (fun ω => (X i ω, e i ω, ε i ω))
      (fun ω => (X 0 ω, e 0 ω, ε 0 ω)) μ μ)
    (hX : MemLp (X 0) 2 μ) (he : MemLp (e 0) 2 μ) (hε : MemLp (ε 0) 2 μ)
    (hXe : IndepFun (X 0) (e 0) μ) (hXε : IndepFun (X 0) (ε 0) μ)
    (heε : IndepFun (e 0) (ε 0) μ)
    (hW : variance (fun ω => X 0 ω + e 0 ω) μ ≠ 0) :
    ∀ᵐ ω ∂μ, Filter.Tendsto (fun n : ℕ => sampleSlopeME X e ε α β n ω) Filter.atTop
      (nhds (β * variance (X 0) μ / (variance (X 0) μ + variance (e 0) μ))) := by
  have h1 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hW0 : MemLp (fun ω => X 0 ω + e 0 ω) 2 μ := hX.add he
  have hβX0 : MemLp (fun ω => β * X 0 ω) 2 μ := hX.const_mul β
  have hY0 : MemLp (fun ω => α + β * X 0 ω + ε 0 ω) 2 μ :=
    ((memLp_const α).add hβX0).add hε
  have hφW : Measurable (fun t : ℝ × ℝ × ℝ => t.1 + t.2.1) := by fun_prop
  have hφY : Measurable (fun t : ℝ × ℝ × ℝ => α + β * t.1 + t.2.2) := by fun_prop
  have hφWY : Measurable
      (fun t : ℝ × ℝ × ℝ => (t.1 + t.2.1) * (α + β * t.1 + t.2.2)) := by fun_prop
  have hφW2 : Measurable (fun t : ℝ × ℝ × ℝ => (t.1 + t.2.1) ^ 2) := by fun_prop
  have iW : Integrable (fun ω => X 0 ω + e 0 ω) μ := hW0.integrable h1
  have iY : Integrable (fun ω => α + β * X 0 ω + ε 0 ω) μ := hY0.integrable h1
  have iWY : Integrable
      (fun ω => (X 0 ω + e 0 ω) * (α + β * X 0 ω + ε 0 ω)) μ :=
    hW0.integrable_mul hY0
  have iW2 : Integrable (fun ω => (X 0 ω + e 0 ω) ^ 2) μ := by
    have h : Integrable (fun ω => (X 0 ω + e 0 ω) * (X 0 ω + e 0 ω)) μ :=
      hW0.integrable_mul hW0
    simpa [pow_two] using h
  have sW := strong_law_ae_real (fun i ω => X i ω + e i ω) iW
    (fun i j hij => (hJoint.indepFun hij).comp hφW hφW)
    (fun i => (hIdent i).comp hφW)
  have sY := strong_law_ae_real (fun i ω => α + β * X i ω + ε i ω) iY
    (fun i j hij => (hJoint.indepFun hij).comp hφY hφY)
    (fun i => (hIdent i).comp hφY)
  have sWY := strong_law_ae_real
    (fun i ω => (X i ω + e i ω) * (α + β * X i ω + ε i ω)) iWY
    (fun i j hij => (hJoint.indepFun hij).comp hφWY hφWY)
    (fun i => (hIdent i).comp hφWY)
  have sW2 := strong_law_ae_real (fun i ω => (X i ω + e i ω) ^ 2) iW2
    (fun i j hij => (hJoint.indepFun hij).comp hφW2 hφW2)
    (fun i => (hIdent i).comp hφW2)
  filter_upwards [sW, sY, sWY, sW2] with ω mW mY mWY mW2
  have hCxy : ∀ n : ℕ, 1 ≤ n →
      (∑ i ∈ Finset.range n, ((X i ω + e i ω)
        - (∑ i ∈ Finset.range n, (X i ω + e i ω)) / (n : ℝ)) *
        ((α + β * X i ω + ε i ω)
        - (∑ i ∈ Finset.range n, (α + β * X i ω + ε i ω)) / (n : ℝ)))
      = (∑ i ∈ Finset.range n, (X i ω + e i ω) * (α + β * X i ω + ε i ω))
        - ((∑ i ∈ Finset.range n, (X i ω + e i ω)) / (n : ℝ))
          * ((∑ i ∈ Finset.range n, (α + β * X i ω + ε i ω)) / (n : ℝ)) * n := by
    intro n hn
    exact centered_sum_div (fun i => X i ω + e i ω)
      (fun i => α + β * X i ω + ε i ω) n hn
  have hCxx : ∀ n : ℕ, 1 ≤ n →
      (∑ i ∈ Finset.range n, ((X i ω + e i ω)
        - (∑ i ∈ Finset.range n, (X i ω + e i ω)) / (n : ℝ)) ^ 2)
      = (∑ i ∈ Finset.range n, (X i ω + e i ω) ^ 2)
        - ((∑ i ∈ Finset.range n, (X i ω + e i ω)) / (n : ℝ))
          * ((∑ i ∈ Finset.range n, (X i ω + e i ω)) / (n : ℝ)) * n := by
    intro n hn
    have h := centered_sum_div (fun i => X i ω + e i ω)
      (fun i => X i ω + e i ω) n hn
    simpa [pow_two] using h
  have hNum : Filter.Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range n, ((X i ω + e i ω)
        - (∑ i ∈ Finset.range n, (X i ω + e i ω)) / (n : ℝ)) *
        ((α + β * X i ω + ε i ω)
        - (∑ i ∈ Finset.range n, (α + β * X i ω + ε i ω)) / (n : ℝ))) / (n : ℝ))
      Filter.atTop
      (nhds ((∫ x, (X 0 x + e 0 x) * (α + β * X 0 x + ε 0 x) ∂μ)
        - (∫ x, (X 0 x + e 0 x) ∂μ) * (∫ x, (α + β * X 0 x + ε 0 x) ∂μ))) := by
    have h := mWY.sub (mW.mul mY)
    refine h.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have hne : n ≠ 0 := by omega
      exact_mod_cast hne
    rw [hCxy n hn, sub_div, mul_div_cancel_right₀ _ hn0]
  have hDen : Filter.Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range n, ((X i ω + e i ω)
        - (∑ i ∈ Finset.range n, (X i ω + e i ω)) / (n : ℝ)) ^ 2) / (n : ℝ))
      Filter.atTop
      (nhds ((∫ x, (X 0 x + e 0 x) ^ 2 ∂μ)
        - (∫ x, (X 0 x + e 0 x) ∂μ) * (∫ x, (X 0 x + e 0 x) ∂μ))) := by
    have h := mW2.sub (mW.mul mW)
    refine h.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have hne : n ≠ 0 := by omega
      exact_mod_cast hne
    rw [hCxx n hn, sub_div, mul_div_cancel_right₀ _ hn0]
  have hL1 : (∫ x, (X 0 x + e 0 x) * (α + β * X 0 x + ε 0 x) ∂μ)
        - (∫ x, (X 0 x + e 0 x) ∂μ) * (∫ x, (α + β * X 0 x + ε 0 x) ∂μ)
      = covariance (fun ω => X 0 ω + e 0 ω)
        (fun ω => α + β * X 0 ω + ε 0 ω) μ := by
    have h := covariance_eq_sub hW0 hY0
    simpa [Pi.mul_apply] using h.symm
  have hL2 : (∫ x, (X 0 x + e 0 x) ^ 2 ∂μ)
        - (∫ x, (X 0 x + e 0 x) ∂μ) * (∫ x, (X 0 x + e 0 x) ∂μ)
      = variance (fun ω => X 0 ω + e 0 ω) μ := by
    have h := variance_eq_sub hW0
    have h2 : (∫ x, (X 0 x + e 0 x) ∂μ) * (∫ x, (X 0 x + e 0 x) ∂μ)
        = (∫ x, (X 0 x + e 0 x) ∂μ) ^ 2 := by ring
    rw [h2]
    simpa [Pi.pow_apply] using h.symm
  have hDen0 : (∫ x, (X 0 x + e 0 x) ^ 2 ∂μ)
      - (∫ x, (X 0 x + e 0 x) ∂μ) * (∫ x, (X 0 x + e 0 x) ∂μ) ≠ 0 := by
    rw [hL2]
    exact hW
  have hRatio := hNum.div hDen hDen0
  have hpop := measurementError_population_attenuation (X := X 0) (e := e 0)
    (ε := ε 0) (α := α) (β := β) hX he hε hXe hXε heε hW
  rw [hL1, hL2] at hRatio
  have hFinal : Filter.Tendsto (fun n : ℕ => sampleSlopeME X e ε α β n ω)
      Filter.atTop
      (nhds (covariance (fun ω => X 0 ω + e 0 ω)
        (fun ω => α + β * X 0 ω + ε 0 ω) μ
        / variance (fun ω => X 0 ω + e 0 ω) μ)) := by
    refine hRatio.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have hne : n ≠ 0 := by omega
      exact_mod_cast hne
    simp only [sampleSlopeME]
    exact div_div_div_cancel_right₀ hn0 _ _
  rw [hpop] at hFinal
  exact hFinal

end MathlibExt.Probability.Statistics.MeasurementErrorAttenuation
