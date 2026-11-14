/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScoreRegression
public import MathlibExt.Probability.Causality.MissingData.GaussianSelection
public import MathlibExt.Probability.Distributions.GaussianCdf
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# LD-score regression on the liability scale for binary traits

For a binary trait (a disease), LD-score regression (Bulik-Sullivan et al. 2015) is run on
case-control association statistics, and the slope estimates a heritability on the observed
`0/1` scale. That number depends on the prevalence and on the case fraction of the sample. It
is reported on the *liability scale* of the threshold model (Falconer 1965): an individual is a
case when a standard normal liability `L` exceeds a threshold `t`. Writing `K = P(L ≥ t)` for the
prevalence and `z = φ(t)` for the standard normal density at the threshold, the conversions are

* population sample (Dempster–Lerner 1950): `h²_l = h²_o · K (1 - K) / z²`;
* case-control sample with case fraction `P` (Lee, Wray, Goddard and Visscher 2011):
  `h²_l = h²_cc · K² (1 - K)² / (P (1 - P) z²)`,

and Bulik-Sullivan et al. convert their observed-scale estimate with the second formula.

## Exact results under the Gaussian threshold model

The usual derivations of both conversions are first-order approximations. Here the observed-scale
quantities are defined as squared correlations (variance explained by the best linear
predictor), and the conversions are then exact:

* `covariance_caseInd`: if `(S, L)` is jointly Gaussian and `L` is standard normal, then
  `Cov(S, 1{L ≥ t}) = Cov(S, L) · φ(t)`. The proof writes `S = Cov(S, L) L + R` with `R`
  uncorrelated with `L`, hence independent of it (joint Gaussianity), and uses the truncated
  mean `𝔼[L 1{L ≥ t}] = φ(t)` (from `GaussianSelection.integral_cond_selectionError_eq`).
* `variance_caseInd`: `Var(1{L ≥ t}) = K (1 - K)`.
* `corrSq_caseInd` (the `R²` conversion of Lee et al. 2012 for polygenic scores): for any score
  `S` jointly Gaussian with `L`, `corr²(S, Y) = corr²(S, L) · z² / (K (1 - K))`.
* `corrSq_genetic_caseInd` and `h2_eq_popLiabilityFactor_mul` (Dempster–Lerner): for a genetic
  value `G` with `Var G = Cov(G, L) = h²` (as for `L = G + E` with `E` independent of `G`, see
  `hasGaussianLaw_liability` and `covariance_liability`), `h²_o = corr²(G, Y) = h² z² / (K (1 - K))`
  and `h² = h²_o · K (1 - K) / z²`.

## Case-control ascertainment

`caseControl μ L t P` is the population law reweighted so that cases have mass `P` and controls
`1 - P`, with the conditional laws of cases and of controls unchanged: the law of a case-control
sample with case fraction `P`. Results:

* `isProbabilityMeasure_caseControl`, `measureReal_case_caseControl` (cases have mass `P`), and
  `caseControl_prevalence` (with `P = K` the sample is the population).
* `covariance_caseControl`: for any square-integrable `S`,
  `Cov_cc(S, Y) = P (1 - P) / (K (1 - K)) · Cov(S, Y)`; no Gaussianity is needed.
* `variance_caseInd_caseControl`: `Var_cc(Y) = P (1 - P)`.
* `caseControlH2Obs_genetic` and `h2_eq_ccLiabilityFactor_mul` (Lee et al. 2011): with
  `h²_cc = Cov_cc(G, Y)² / (Var G · Var_cc(Y))`, `h²_cc = h² P (1 - P) z² / (K² (1 - K)²)` and
  `h² = h²_cc · K² (1 - K)² / (P (1 - P) z²)` exactly.

## Liability-scale LD-score regression

`liabilityH2Hat t P N M ℓ χ` is T147's unweighted estimator `olsH2Hat` multiplied by the
case-control conversion factor. If the case-control statistics follow T147's regression model
with observed-scale heritability `h²_cc` of a liability model with heritability `h²`, then:

* `liabilityH2Hat_integral_chiSqStrat` (population version) returns `h²`;
* `integral_liabilityH2Hat_chiSqStrat` (unbiasedness): `𝔼[ĥ²_l] = h²`;
* `tendstoInMeasure_liabilityH2Hat` (consistency): `ĥ²_l → h²` in probability when the variance of
  the observed-scale estimator tends to `0`.

## What is assumed rather than derived

The threshold is the parameter: `K = Φ(-t)`, so `t = Φ⁻¹(1 - K)`. The observed-scale heritability
is the squared correlation of the trait with the genetic value. In the case-control version its
denominator uses the population genetic variance `Var G`, as in Lee et al. (2011); ascertainment
also changes the genetic variance within the sample, and that change is not modeled.
The step from binary case-control statistics to T147's regression model (`χ²_j` satisfying the
LD-score regression identity with heritability `h²_cc`) is the approximation made by
Bulik-Sullivan et al. and is a hypothesis here (`hobs`): the binary trait is not a linear
model in the genotypes, so T147's model does not hold for it exactly. Weighted least squares and
the paper's intercept handling are not treated (see `LDScoreRegression`).

## References

* E. R. Dempster and I. M. Lerner, *Heritability of threshold characters*, Genetics 35 (1950),
  212–236.
* D. S. Falconer, *The inheritance of liability to certain diseases, estimated from the incidence
  among relatives*, Ann. Hum. Genet. 29 (1965), 51–76.
* S. H. Lee, N. R. Wray, M. E. Goddard and P. M. Visscher, *Estimating missing heritability for
  disease from genome-wide association studies*, Am. J. Hum. Genet. 88 (2011), 294–305.
* S. H. Lee, M. E. Goddard, N. R. Wray and P. M. Visscher, *A better coefficient of determination
  for genetic profile analysis*, Genet. Epidemiol. 36 (2012), 214–224.
* B. K. Bulik-Sullivan et al., *LD Score regression distinguishes confounding from polygenicity in
  genome-wide association studies*, Nat. Genet. 47 (2015), 291–295.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open MathlibExt.Biology.StatisticalGenetics.LDScore
  MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
  MathlibExt.Biology.StatisticalGenetics.LDScoreRegression
  MathlibExt.Probability.FiniteProbability MathlibExt.Probability.ConvergenceInProbability
  MathlibExt.Probability.Causality.MissingData

namespace MathlibExt.Biology.StatisticalGenetics.LDScoreLiability

/-! ### Threshold quantities -/

/-- The **prevalence** `K = P(L ≥ t) = Φ(-t)` of the threshold model with threshold `t` and
standard normal liability `L`. -/
noncomputable def prevalence (t : ℝ) : ℝ := cdf (gaussianReal 0 1) (-t)

/-- The standard normal density `z = φ(t)` at the threshold `t`. -/
noncomputable def thresholdDensity (t : ℝ) : ℝ := gaussianPDFReal 0 1 t

theorem prevalence_pos (t : ℝ) : 0 < prevalence t :=
  (cdf_nonneg _ (-t - 1)).trans_lt
    (strictMono_cdf_gaussianReal 0 one_ne_zero (by linarith : -t - 1 < -t))

theorem prevalence_lt_one (t : ℝ) : prevalence t < 1 :=
  (strictMono_cdf_gaussianReal 0 one_ne_zero (by linarith : -t < -t + 1)).trans_le
    (cdf_le_one _ _)

theorem thresholdDensity_pos (t : ℝ) : 0 < thresholdDensity t :=
  gaussianPDFReal_pos 0 1 t one_ne_zero

theorem thresholdDensity_neg (t : ℝ) : thresholdDensity (-t) = thresholdDensity t := by
  simp only [thresholdDensity, gaussianPDFReal_def, sub_zero, even_two, Even.neg_pow]

/-- The population (Dempster–Lerner) conversion factor `K (1 - K) / z²`. -/
noncomputable def popLiabilityFactor (t : ℝ) : ℝ :=
  prevalence t * (1 - prevalence t) / thresholdDensity t ^ 2

/-- The case-control conversion factor `K² (1 - K)² / (P (1 - P) z²)` of Lee et al. (2011), for
case fraction `P`. -/
noncomputable def ccLiabilityFactor (t P : ℝ) : ℝ :=
  prevalence t ^ 2 * (1 - prevalence t) ^ 2 / (P * (1 - P) * thresholdDensity t ^ 2)

/-- With case fraction equal to the prevalence, the case-control factor is the population
factor. -/
theorem ccLiabilityFactor_prevalence (t : ℝ) :
    ccLiabilityFactor t (prevalence t) = popLiabilityFactor t := by
  have hK := prevalence_pos t
  have hK1 : 1 - prevalence t ≠ 0 := (sub_pos.mpr (prevalence_lt_one t)).ne'
  have hz := (thresholdDensity_pos t).ne'
  unfold ccLiabilityFactor popLiabilityFactor
  field_simp

/-! ### The liability threshold model -/

section Liability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The **case indicator** `Y = 1{L ≥ t}` of the threshold model. -/
noncomputable def caseInd (L : Ω → ℝ) (t : ℝ) : Ω → ℝ := {ω | t ≤ L ω}.indicator fun _ => 1

theorem caseInd_eq_comp (L : Ω → ℝ) (t : ℝ) :
    caseInd L t = (Set.Ici t).indicator (fun _ => (1 : ℝ)) ∘ L := by
  ext ω
  simp [caseInd, Set.indicator_apply]

theorem caseInd_sq (L : Ω → ℝ) (t : ℝ) : caseInd L t ^ 2 = caseInd L t := by
  ext ω
  by_cases h : t ≤ L ω <;> simp [caseInd, h]

theorem measurableSet_case {L : Ω → ℝ} (hLm : Measurable L) (t : ℝ) :
    MeasurableSet {ω | t ≤ L ω} :=
  hLm measurableSet_Ici

theorem memLp_caseInd {L : Ω → ℝ} (hLm : Measurable L) (t : ℝ) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) : MemLp (caseInd L t) p μ :=
  memLp_indicator_const p (measurableSet_case hLm t).nullMeasurableSet 1
    (Or.inr (measure_ne_top _ _))

/-- Fraction of the population that are cases (the prevalence). -/
theorem measureReal_case [IsProbabilityMeasure μ] {L : Ω → ℝ}
    (hL : HasLaw L (gaussianReal 0 1) μ) (t : ℝ) :
    μ.real {ω | t ≤ L ω} = prevalence t := by
  have h := measureReal_selection_eq_cdf (c := -t) hL
  simpa only [neg_neg, prevalence] using h

theorem integral_caseInd [IsProbabilityMeasure μ] {L : Ω → ℝ}
    (hL : HasLaw L (gaussianReal 0 1) μ) (hLm : Measurable L) (t : ℝ) :
    μ[caseInd L t] = prevalence t := by
  rw [caseInd, integral_indicator_const _ (measurableSet_case hLm t), smul_eq_mul, mul_one,
    measureReal_case hL t]

/-- The truncated first moment `𝔼[L 1{L ≥ t}] = φ(t)`. -/
theorem integral_mul_caseInd [IsProbabilityMeasure μ] {L : Ω → ℝ}
    (hL : HasLaw L (gaussianReal 0 1) μ) (hLm : Measurable L) (t : ℝ) :
    μ[L * caseInd L t] = thresholdDensity t := by
  set s := {ω | t ≤ L ω} with hs_def
  have hs : MeasurableSet s := measurableSet_case hLm t
  have h := integral_cond_selectionError_eq (c := -t) hL hLm
  simp only [neg_neg] at h
  have hcond : μ[|s] = (μ s)⁻¹ • μ.restrict s := rfl
  rw [hcond, integral_smul_measure, ENNReal.toReal_inv, ← Measure.real_def,
    measureReal_case hL t, smul_eq_mul, inverseMillsRatio] at h
  have hK := (prevalence_pos t).ne'
  change _ = gaussianPDFReal 0 1 (-t) / prevalence t at h
  have hint : ∫ ω in s, L ω ∂μ = thresholdDensity t := by
    rw [← thresholdDensity_neg, thresholdDensity]
    calc ∫ ω in s, L ω ∂μ = prevalence t * ((prevalence t)⁻¹ * ∫ ω in s, L ω ∂μ) := by
          rw [← mul_assoc, mul_inv_cancel₀ hK, one_mul]
      _ = prevalence t * (gaussianPDFReal 0 1 (-t) / prevalence t) := by rw [h]
      _ = gaussianPDFReal 0 1 (-t) := by field_simp
  have hfun : L * caseInd L t = s.indicator L := by
    ext ω
    by_cases hω : t ≤ L ω <;> simp [caseInd, s, hω]
  rw [hfun, integral_indicator hs, hint]

theorem memLp_of_hasLaw_std {L : Ω → ℝ} (hL : HasLaw L (gaussianReal 0 1) μ) :
    MemLp L 2 μ := by
  simpa using hL.memLp (memLp_id_gaussianReal 2)

theorem integral_of_hasLaw_std {L : Ω → ℝ} (hL : HasLaw L (gaussianReal 0 1) μ) :
    μ[L] = 0 := by
  rw [hL.integral_eq, integral_id_gaussianReal]

theorem variance_of_hasLaw_std {L : Ω → ℝ} (hL : HasLaw L (gaussianReal 0 1) μ) :
    Var[L; μ] = 1 := by
  rw [hL.variance_eq, variance_id_gaussianReal, NNReal.coe_one]

/-- `Cov(L, 1{L ≥ t}) = φ(t)`. -/
theorem covariance_self_caseInd [IsProbabilityMeasure μ] {L : Ω → ℝ}
    (hL : HasLaw L (gaussianReal 0 1) μ) (hLm : Measurable L) (t : ℝ) :
    cov[L, caseInd L t; μ] = thresholdDensity t := by
  rw [covariance_eq_sub (memLp_of_hasLaw_std hL) (memLp_caseInd hLm t 2),
    integral_mul_caseInd hL hLm t, integral_of_hasLaw_std hL, zero_mul, sub_zero]

/-- **Variance of the case indicator**: `Var(1{L ≥ t}) = K (1 - K)`. -/
theorem variance_caseInd [IsProbabilityMeasure μ] {L : Ω → ℝ}
    (hL : HasLaw L (gaussianReal 0 1) μ) (hLm : Measurable L) (t : ℝ) :
    Var[caseInd L t; μ] = prevalence t * (1 - prevalence t) := by
  rw [variance_eq_sub (memLp_caseInd hLm t 2), caseInd_sq, integral_caseInd hL hLm t]
  ring

/-- **Covariance with the case indicator.** If `(S, L)` is jointly Gaussian and `L` is standard
normal, then `Cov(S, 1{L ≥ t}) = Cov(S, L) · φ(t)`. -/
theorem covariance_caseInd [IsProbabilityMeasure μ] {S L : Ω → ℝ}
    (hSL : HasGaussianLaw (fun ω => (S ω, L ω)) μ) (hL : HasLaw L (gaussianReal 0 1) μ)
    (hLm : Measurable L) (t : ℝ) :
    cov[S, caseInd L t; μ] = cov[S, L; μ] * thresholdDensity t := by
  set c := cov[S, L; μ] with hc
  have hS2 : MemLp S 2 μ := hSL.fst.memLp_two
  have hL2 : MemLp L 2 μ := memLp_of_hasLaw_std hL
  have hY2 : MemLp (caseInd L t) 2 μ := memLp_caseInd hLm t 2
  set R : Ω → ℝ := S - c • L with hR
  have hR2 : MemLp R 2 μ := hS2.sub (hL2.const_smul c)
  -- `(R, L)` is a linear image of `(S, L)`, hence jointly Gaussian.
  let T : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ - c • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hRL : HasGaussianLaw (fun ω => (R ω, L ω)) μ := by
    exact (hSL.map_fun T).congr (ae_of_all _ fun ω => by simp [T, R])
  have hcovRL : cov[R, L; μ] = 0 := by
    rw [hR, covariance_sub_left hS2 (hL2.const_smul c) hL2, covariance_smul_left,
      covariance_self hLm.aemeasurable, variance_of_hasLaw_std hL, ← hc]
    ring
  have hind : IndepFun R L μ := hRL.indepFun_of_covariance_eq_zero hcovRL
  have hindY : IndepFun R (caseInd L t) μ := by
    rw [caseInd_eq_comp]
    exact hind.comp measurable_id (measurable_const.indicator measurableSet_Ici)
  have hRY : cov[R, caseInd L t; μ] = 0 := hindY.covariance_eq_zero hR2 hY2
  have hSeq : S = R + c • L := by
    ext ω
    simp [R]
  rw [hSeq, covariance_add_left hR2 (hL2.const_smul c) hY2, hRY, covariance_smul_left,
    covariance_self_caseInd hL hLm t]
  ring

/-- The squared correlation `Cov(X, Y)² / (Var X · Var Y)`: the fraction of the variance of `Y`
explained by the best linear predictor from `X` (Lean's `x / 0 = 0` makes it `0` when either
variance vanishes). -/
noncomputable def corrSq (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  cov[X, Y; μ] ^ 2 / (Var[X; μ] * Var[Y; μ])

/-- **Observed versus liability `R²`** (Lee et al. 2012). For a score `S` jointly Gaussian with
the standard normal liability `L`, `corr²(S, Y) = corr²(S, L) · z² / (K (1 - K))`. -/
theorem corrSq_caseInd [IsProbabilityMeasure μ] {S L : Ω → ℝ}
    (hSL : HasGaussianLaw (fun ω => (S ω, L ω)) μ) (hL : HasLaw L (gaussianReal 0 1) μ)
    (hLm : Measurable L) (t : ℝ) :
    corrSq μ S (caseInd L t) =
      corrSq μ S L * (thresholdDensity t ^ 2 / (prevalence t * (1 - prevalence t))) := by
  unfold corrSq
  rw [covariance_caseInd hSL hL hLm t, variance_caseInd hL hLm t, variance_of_hasLaw_std hL,
    mul_pow, mul_one, div_mul_div_comm]

/-- The liability-scale `R²` of a score from its observed-scale `R²`:
`corr²(S, L) = corr²(S, Y) · K (1 - K) / z²`. -/
theorem corrSq_liability_eq [IsProbabilityMeasure μ] {S L : Ω → ℝ}
    (hSL : HasGaussianLaw (fun ω => (S ω, L ω)) μ) (hL : HasLaw L (gaussianReal 0 1) μ)
    (hLm : Measurable L) (t : ℝ) :
    corrSq μ S L = corrSq μ S (caseInd L t) * popLiabilityFactor t := by
  have hK := (prevalence_pos t).ne'
  have hK1 : 1 - prevalence t ≠ 0 := (sub_pos.mpr (prevalence_lt_one t)).ne'
  have hz := (thresholdDensity_pos t).ne'
  rw [corrSq_caseInd hSL hL hLm t, popLiabilityFactor]
  field_simp

private theorem corrSq_genetic_self {G L : Ω → ℝ} {h2 : ℝ} (hL : HasLaw L (gaussianReal 0 1) μ)
    (hvar : Var[G; μ] = h2) (hcov : cov[G, L; μ] = h2) : corrSq μ G L = h2 := by
  unfold corrSq
  rw [hvar, hcov, variance_of_hasLaw_std hL]
  rcases eq_or_ne h2 0 with h | h
  · simp [h]
  · field_simp

/-- **Dempster–Lerner, exact form.** For a genetic value `G` with `Var G = Cov(G, L) = h²`
jointly Gaussian with the standard normal liability `L`, the observed-scale heritability
`h²_o = corr²(G, 1{L ≥ t})` equals `h² z² / (K (1 - K))`. -/
theorem corrSq_genetic_caseInd [IsProbabilityMeasure μ] {G L : Ω → ℝ}
    (hGL : HasGaussianLaw (fun ω => (G ω, L ω)) μ) (hL : HasLaw L (gaussianReal 0 1) μ)
    (hLm : Measurable L) (t : ℝ) {h2 : ℝ} (hvar : Var[G; μ] = h2) (hcov : cov[G, L; μ] = h2) :
    corrSq μ G (caseInd L t) =
      h2 * (thresholdDensity t ^ 2 / (prevalence t * (1 - prevalence t))) := by
  rw [corrSq_caseInd hGL hL hLm t, corrSq_genetic_self hL hvar hcov]

/-- **Dempster–Lerner conversion**: `h² = h²_o · K (1 - K) / z²`. -/
theorem h2_eq_popLiabilityFactor_mul [IsProbabilityMeasure μ] {G L : Ω → ℝ}
    (hGL : HasGaussianLaw (fun ω => (G ω, L ω)) μ) (hL : HasLaw L (gaussianReal 0 1) μ)
    (hLm : Measurable L) (t : ℝ) {h2 : ℝ} (hvar : Var[G; μ] = h2) (hcov : cov[G, L; μ] = h2) :
    h2 = popLiabilityFactor t * corrSq μ G (caseInd L t) := by
  rw [mul_comm, ← corrSq_liability_eq hGL hL hLm t, corrSq_genetic_self hL hvar hcov]

/-- The textbook liability model `L = G + E` with independent Gaussian `G` and `E` gives a
jointly Gaussian pair `(G, L)`. -/
theorem hasGaussianLaw_liability {G E : Ω → ℝ} (hG : HasGaussianLaw G μ)
    (hE : HasGaussianLaw E μ) (hGE : IndepFun G E μ) :
    HasGaussianLaw (fun ω => (G ω, G ω + E ω)) μ := by
  let T : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)
  exact ((hGE.hasGaussianLaw hG hE).map_fun T).congr (ae_of_all _ fun ω => by simp [T])

/-- In the model `L = G + E` with `G` and `E` independent, `Cov(G, L) = Var G`. -/
theorem covariance_liability {G E : Ω → ℝ} [IsProbabilityMeasure μ] (hG : MemLp G 2 μ)
    (hE : MemLp E 2 μ) (hGE : IndepFun G E μ) :
    cov[G, fun ω => G ω + E ω; μ] = Var[G; μ] := by
  have h := covariance_add_right hG hG hE
  simp only [Pi.add_def] at h
  rw [h, hGE.covariance_eq_zero hG hE, add_zero, covariance_self hG.aemeasurable]

end Liability

/-! ### Case-control ascertainment -/

section CaseControl

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The law of a **case-control sample** with case fraction `P`: the population law `μ`
reweighted so that cases `{t ≤ L}` have total mass `P` and controls `1 - P`, keeping the
conditional laws within cases and within controls. -/
noncomputable def caseControl (μ : Measure Ω) (L : Ω → ℝ) (t P : ℝ) : Measure Ω :=
  (P / μ.real {ω | t ≤ L ω}).toNNReal • μ.restrict {ω | t ≤ L ω} +
    ((1 - P) / (1 - μ.real {ω | t ≤ L ω})).toNNReal • μ.restrict {ω | t ≤ L ω}ᶜ

variable {L : Ω → ℝ} {t P : ℝ}

/-- Expectations under the case-control law. -/
theorem integral_caseControl (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hk1 : μ.real {ω | t ≤ L ω} < 1)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∫ ω, f ω ∂caseControl μ L t P =
      P / μ.real {ω | t ≤ L ω} * ∫ ω in {ω | t ≤ L ω}, f ω ∂μ +
        (1 - P) / (1 - μ.real {ω | t ≤ L ω}) * ∫ ω in {ω | t ≤ L ω}ᶜ, f ω ∂μ := by
  have hk0 : 0 ≤ μ.real {ω | t ≤ L ω} := measureReal_nonneg
  rw [caseControl, integral_add_measure (hf.restrict.smul_measure_nnreal)
    (hf.restrict.smul_measure_nnreal), integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    NNReal.smul_def, NNReal.smul_def, Real.coe_toNNReal _ (div_nonneg hP0 hk0),
    Real.coe_toNNReal _ (div_nonneg (by linarith) (by linarith)), smul_eq_mul, smul_eq_mul]

theorem memLp_caseControl {f : Ω → ℝ} {p : ℝ≥0∞} (hf : MemLp f p μ) :
    MemLp f p (caseControl μ L t P) :=
  ((hf.restrict _).smul_measure_nnreal).add_measure ((hf.restrict _).smul_measure_nnreal)

theorem measureReal_compl_case [IsProbabilityMeasure μ] (hLm : Measurable L) :
    μ.real {ω | t ≤ L ω}ᶜ = 1 - μ.real {ω | t ≤ L ω} := by
  rw [measureReal_compl (measurableSet_case hLm t), probReal_univ]

/-- The case-control law is a probability measure when `0 < K < 1` and `0 ≤ P ≤ 1`. -/
theorem isProbabilityMeasure_caseControl [IsProbabilityMeasure μ] (hLm : Measurable L)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1)
    (hk0 : 0 < μ.real {ω | t ≤ L ω}) (hk1 : μ.real {ω | t ≤ L ω} < 1) :
    IsProbabilityMeasure (caseControl μ L t P) := by
  constructor
  have hint := integral_caseControl (L := L) (t := t) hP0 hP1 hk1
    (integrable_const (μ := μ) (1 : ℝ))
  rw [integral_const, setIntegral_const, setIntegral_const, measureReal_compl_case hLm] at hint
  simp only [smul_eq_mul, mul_one] at hint
  have h1 : (caseControl μ L t P).real Set.univ = 1 := by
    rw [hint]
    field_simp
    ring
  have hfin : (caseControl μ L t P) Set.univ ≠ ∞ := by
    unfold caseControl
    simp [Measure.add_apply, ENNReal.mul_eq_top, measure_ne_top]
  rw [← ENNReal.ofReal_toReal hfin, ← Measure.real_def, h1, ENNReal.ofReal_one]

/-- Cases have mass `P` under the case-control law. -/
theorem measureReal_case_caseControl [IsProbabilityMeasure μ] (hLm : Measurable L)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1)
    (hk0 : 0 < μ.real {ω | t ≤ L ω}) (hk1 : μ.real {ω | t ≤ L ω} < 1) :
    (caseControl μ L t P).real {ω | t ≤ L ω} = P := by
  have h := integral_caseControl (L := L) (t := t) hP0 hP1 hk1
    ((memLp_caseInd (μ := μ) hLm t 1).integrable le_rfl)
  rw [caseInd, integral_indicator_const _ (measurableSet_case hLm t), smul_eq_mul, mul_one] at h
  rw [h, setIntegral_indicator (measurableSet_case hLm t), Set.inter_self, setIntegral_const,
    setIntegral_indicator (measurableSet_case hLm t), Set.compl_inter_self, setIntegral_const]
  simp only [smul_eq_mul, mul_one, measureReal_empty, mul_zero, add_zero]
  field_simp [hk0.ne']

/-- With case fraction `P = K`, the case-control sample is the population. -/
theorem caseControl_prevalence (hLm : Measurable L) (hk0 : 0 < μ.real {ω | t ≤ L ω})
    (hk1 : μ.real {ω | t ≤ L ω} < 1) :
    caseControl μ L t (μ.real {ω | t ≤ L ω}) = μ := by
  rw [caseControl, div_self hk0.ne', div_self (sub_pos.mpr hk1).ne', Real.toNNReal_one, one_smul,
    one_smul, Measure.restrict_add_restrict_compl (measurableSet_case hLm t)]

/-- **Covariance under case-control ascertainment.** For any square-integrable `S`,
`Cov_cc(S, Y) = P (1 - P) / (K (1 - K)) · Cov(S, Y)`, with `Y` the case indicator and `K` the
population fraction of cases. -/
theorem covariance_caseControl [IsProbabilityMeasure μ] (hLm : Measurable L)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1)
    (hk0 : 0 < μ.real {ω | t ≤ L ω}) (hk1 : μ.real {ω | t ≤ L ω} < 1) {S : Ω → ℝ}
    (hS : MemLp S 2 μ) :
    cov[S, caseInd L t; caseControl μ L t P] =
      P * (1 - P) / (μ.real {ω | t ≤ L ω} * (1 - μ.real {ω | t ≤ L ω})) *
        cov[S, caseInd L t; μ] := by
  have := isProbabilityMeasure_caseControl hLm hP0 hP1 hk0 hk1
  set s := {ω | t ≤ L ω} with hs_def
  have hs : MeasurableSet s := measurableSet_case hLm t
  set k := μ.real s with hk_def
  have hY2 : MemLp (caseInd L t) 2 μ := memLp_caseInd hLm t 2
  have hSY : Integrable (S * caseInd L t) μ := hS.integrable_mul hY2
  have hSi : Integrable S μ := hS.integrable one_le_two
  have hYi : Integrable (caseInd L t) μ := hY2.integrable one_le_two
  -- the integrands restricted to cases and to controls
  have hY_case : Set.EqOn (caseInd L t) (fun _ => (1 : ℝ)) s := fun ω hω =>
    Set.indicator_of_mem hω _
  have hY_ctrl : Set.EqOn (caseInd L t) (fun _ => (0 : ℝ)) sᶜ := fun ω hω =>
    Set.indicator_of_notMem hω _
  have hSY_case : ∫ ω in s, (S * caseInd L t) ω ∂μ = ∫ ω in s, S ω ∂μ :=
    setIntegral_congr_fun hs fun ω hω => by simp [Pi.mul_apply, hY_case hω]
  have hSY_ctrl : ∫ ω in sᶜ, (S * caseInd L t) ω ∂μ = 0 := by
    rw [setIntegral_congr_fun (g := fun _ => (0 : ℝ)) hs.compl
      fun ω hω => by simp [Pi.mul_apply, hY_ctrl hω]]
    simp
  have hY_case_int : ∫ ω in s, caseInd L t ω ∂μ = k := by
    rw [setIntegral_congr_fun hs hY_case, setIntegral_const, smul_eq_mul, mul_one]
  have hY_ctrl_int : ∫ ω in sᶜ, caseInd L t ω ∂μ = 0 := by
    rw [setIntegral_congr_fun hs.compl hY_ctrl]
    simp
  have hEY : μ[caseInd L t] = k := by
    rw [caseInd, integral_indicator_const _ hs, smul_eq_mul, mul_one]
  have hES := integral_add_compl hs hSi
  have hESY := integral_add_compl hs hSY
  rw [hSY_case, hSY_ctrl, add_zero] at hESY
  rw [covariance_eq_sub (memLp_caseControl hS) (memLp_caseControl hY2),
    covariance_eq_sub hS hY2, integral_caseControl hP0 hP1 hk1 hSY,
    integral_caseControl hP0 hP1 hk1 hSi, integral_caseControl hP0 hP1 hk1 hYi, ← hs_def,
    ← hk_def, hSY_case,
    hSY_ctrl, hY_case_int, hY_ctrl_int, hEY, ← hESY, ← hES]
  have hk1' : 1 - k ≠ 0 := (sub_pos.mpr hk1).ne'
  field_simp
  ring

/-- Under the case-control law the case indicator has variance `P (1 - P)`. -/
theorem variance_caseInd_caseControl [IsProbabilityMeasure μ] (hLm : Measurable L)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1)
    (hk0 : 0 < μ.real {ω | t ≤ L ω}) (hk1 : μ.real {ω | t ≤ L ω} < 1) :
    Var[caseInd L t; caseControl μ L t P] = P * (1 - P) := by
  have := isProbabilityMeasure_caseControl hLm hP0 hP1 hk0 hk1
  have hE : (caseControl μ L t P)[caseInd L t] = P := by
    rw [caseInd, integral_indicator_const _ (measurableSet_case hLm t), smul_eq_mul, mul_one,
      measureReal_case_caseControl hLm hP0 hP1 hk0 hk1]
  rw [variance_eq_sub (memLp_caseInd hLm t 2), caseInd_sq, hE]
  ring

/-- The **case-control observed-scale heritability** of Lee et al. (2011): the squared
covariance of the genetic value `G` and the case indicator in the case-control sample, divided by
the population genetic variance and the case-control variance of the case indicator. -/
noncomputable def caseControlH2Obs (μ : Measure Ω) (L G : Ω → ℝ) (t P : ℝ) : ℝ :=
  cov[G, caseInd L t; caseControl μ L t P] ^ 2 /
    (Var[G; μ] * Var[caseInd L t; caseControl μ L t P])

/-- **Lee et al. (2011), exact form.** For a genetic value `G` with `Var G = Cov(G, L) = h²`
jointly Gaussian with the standard normal liability `L`, and a case fraction `0 < P < 1`,
`h²_cc = h² P (1 - P) z² / (K² (1 - K)²)`. -/
theorem caseControlH2Obs_genetic [IsProbabilityMeasure μ] {G : Ω → ℝ}
    (hGL : HasGaussianLaw (fun ω => (G ω, L ω)) μ)
    (hL : HasLaw L (gaussianReal 0 1) μ) (hLm : Measurable L) (hP0 : 0 < P) (hP1 : P < 1)
    {h2 : ℝ} (hvar : Var[G; μ] = h2) (hcov : cov[G, L; μ] = h2) :
    caseControlH2Obs μ L G t P = h2 * (P * (1 - P) * thresholdDensity t ^ 2 /
      (prevalence t ^ 2 * (1 - prevalence t) ^ 2)) := by
  have hk := measureReal_case hL t
  have hk0 : 0 < μ.real {ω | t ≤ L ω} := hk ▸ prevalence_pos t
  have hk1 : μ.real {ω | t ≤ L ω} < 1 := hk ▸ prevalence_lt_one t
  unfold caseControlH2Obs
  rw [covariance_caseControl hLm hP0.le hP1.le hk0 hk1 hGL.fst.memLp_two,
    variance_caseInd_caseControl hLm hP0.le hP1.le hk0 hk1, covariance_caseInd hGL hL hLm t,
    hvar, hcov, hk]
  have hK := (prevalence_pos t).ne'
  have hK1 : 1 - prevalence t ≠ 0 := (sub_pos.mpr (prevalence_lt_one t)).ne'
  have hP' : P ≠ 0 := hP0.ne'
  have hP1' : 1 - P ≠ 0 := (sub_pos.mpr hP1).ne'
  rcases eq_or_ne h2 0 with h | h
  · simp [h]
  · field_simp

/-- **Case-control conversion** (Lee et al. 2011): `h² = h²_cc · K² (1 - K)² / (P (1 - P) z²)`. -/
theorem h2_eq_ccLiabilityFactor_mul [IsProbabilityMeasure μ] {G : Ω → ℝ}
    (hGL : HasGaussianLaw (fun ω => (G ω, L ω)) μ) (hL : HasLaw L (gaussianReal 0 1) μ)
    (hLm : Measurable L) (hP0 : 0 < P) (hP1 : P < 1) {h2 : ℝ} (hvar : Var[G; μ] = h2)
    (hcov : cov[G, L; μ] = h2) :
    h2 = ccLiabilityFactor t P * caseControlH2Obs μ L G t P := by
  rw [caseControlH2Obs_genetic hGL hL hLm hP0 hP1 hvar hcov, ccLiabilityFactor]
  have hK := (prevalence_pos t).ne'
  have hK1 : 1 - prevalence t ≠ 0 := (sub_pos.mpr (prevalence_lt_one t)).ne'
  have hz := (thresholdDensity_pos t).ne'
  have hP' : P ≠ 0 := hP0.ne'
  have hP1' : 1 - P ≠ 0 := (sub_pos.mpr hP1).ne'
  field_simp

end CaseControl

/-! ### Liability-scale LD-score regression -/

/-- The **liability-scale LD-score regression estimator** for a case-control study with case
fraction `P` and threshold `t` (prevalence `K = Φ(-t)`): T147's unweighted estimator `olsH2Hat`
times the conversion factor `K² (1 - K)² / (P (1 - P) z²)`. -/
noncomputable def liabilityH2Hat (t P : ℝ) (N M : ℕ) (ℓ χ : Fin M → ℝ) : ℝ :=
  ccLiabilityFactor t P * olsH2Hat N M ℓ χ

section LDSC

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {Ξ : Type*} {mΞ : MeasurableSpace Ξ} {ν : Measure Ξ} {N M : ℕ}

/-- **Population consistency on the liability scale.** If the expected case-control statistics
follow T147's regression model whose heritability is the case-control observed-scale
heritability of a liability model with heritability `h²` (hypothesis `hobs`), then the
liability-scale estimator applied to the expected statistics returns `h²`. -/
theorem liabilityH2Hat_integral_chiSqStrat [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L G : Ξ → ℝ} {t P h2 : ℝ}
    (hGL : HasGaussianLaw (fun ω => (G ω, L ω)) ν) (hL : HasLaw L (gaussianReal 0 1) ν)
    (hLm : Measurable L) (hP0 : 0 < P) (hP1 : P < 1) (hvar : Var[G; ν] = h2)
    (hcov : cov[G, L; ν] = h2)
    (D : Model μ N M) (hobs : D.h2 = caseControlH2Obs ν L G t P)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hM : M ≠ 0) (hX : IsStandardized X)
    (hℓ : sxy (ldScore X) (ldScore X) ≠ 0)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) :
    liabilityH2Hat t P N M (ldScore X) (fun j => ∫ ω, chiSqStrat D X s c j ω ∂μ) = h2 := by
  rw [liabilityH2Hat, olsH2Hat_integral_chiSqStrat D X hN hM hX hℓ hβ hε s c ha, hobs]
  exact (h2_eq_ccLiabilityFactor_mul hGL hL hLm hP0 hP1 hvar hcov).symm

/-- **Unbiasedness on the liability scale.** Under the hypotheses of
`liabilityH2Hat_integral_chiSqStrat`, `𝔼[ĥ²_l] = h²`. -/
theorem integral_liabilityH2Hat_chiSqStrat [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L G : Ξ → ℝ} {t P h2 : ℝ}
    (hGL : HasGaussianLaw (fun ω => (G ω, L ω)) ν) (hL : HasLaw L (gaussianReal 0 1) ν)
    (hLm : Measurable L) (hP0 : 0 < P) (hP1 : P < 1) (hvar : Var[G; ν] = h2)
    (hcov : cov[G, L; ν] = h2)
    (D : Model μ N M) (hobs : D.h2 = caseControlH2Obs ν L G t P)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hM : M ≠ 0) (hX : IsStandardized X)
    (hℓ : sxy (ldScore X) (ldScore X) ≠ 0)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) :
    ∫ ω, liabilityH2Hat t P N M (ldScore X) (fun j => chiSqStrat D X s c j ω) ∂μ = h2 := by
  simp only [liabilityH2Hat]
  rw [integral_const_mul, integral_olsH2Hat_chiSqStrat D X hN hM hX hℓ hβ hε s c ha, hobs]
  exact (h2_eq_ccLiabilityFactor_mul hGL hL hLm hP0 hP1 hvar hcov).symm

/-- **Consistency on the liability scale.** Along a sequence of designs and observed-scale
models whose common heritability is the case-control observed-scale heritability of a liability
model with heritability `h²`, if the variance of the observed-scale estimator tends to `0`, then
the liability-scale estimator converges in probability to `h²`. -/
theorem tendstoInMeasure_liabilityH2Hat [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L G : Ξ → ℝ} {t P h2 : ℝ}
    (hGL : HasGaussianLaw (fun ω => (G ω, L ω)) ν) (hL : HasLaw L (gaussianReal 0 1) ν)
    (hLm : Measurable L) (hP0 : 0 < P) (hP1 : P < 1) (hvar : Var[G; ν] = h2)
    (hcov : cov[G, L; ν] = h2)
    {ι : Type*} {l : Filter ι}
    {N M : ι → ℕ} (D : ∀ n, Model μ (N n) (M n)) (X : ∀ n, Matrix (Fin (N n)) (Fin (M n)) ℝ)
    (hobs : ∀ n, (D n).h2 = caseControlH2Obs ν L G t P) (hN : ∀ n, N n ≠ 0)
    (hM : ∀ n, M n ≠ 0)
    (hX : ∀ n, IsStandardized (X n)) (hℓ : ∀ n, sxy (ldScore (X n)) (ldScore (X n)) ≠ 0)
    (hβ : ∀ n k, ∫ ω, (D n).beta k ω ∂μ = 0) (hε : ∀ n i, ∫ ω, (D n).eps i ω ∂μ = 0)
    (s : ι → ℝ) (c : ∀ n, Fin (N n) → ℝ) (a : ι → ℝ)
    (ha : ∀ n j, s n ^ 2 * ((∑ i, X n i j * c n i) / N n) ^ 2 = a n)
    (hvarT : Tendsto (fun n => evariance (fun ω =>
      olsH2Hat (N n) (M n) (ldScore (X n)) fun j => chiSqStrat (D n) (X n) (s n) (c n) j ω) μ)
      l (𝓝 0)) :
    TendstoInMeasure μ (fun n ω =>
      liabilityH2Hat t P (N n) (M n) (ldScore (X n)) fun j =>
        chiSqStrat (D n) (X n) (s n) (c n) j ω)
      l fun _ => h2 := by
  refine tendstoInMeasure_of_integral_eq_of_evariance
    (fun n => ((integrable_olsH2Hat_chiSqStrat (D n) (X n) (s n) (c n)).const_mul
      _).aestronglyMeasurable)
    (fun n => integral_liabilityH2Hat_chiSqStrat hGL hL hLm hP0 hP1 hvar hcov (D n) (hobs n)
      (X n) (hN n) (hM n) (hX n) (hℓ n) (hβ n) (hε n) (s n) (c n) (ha n)) ?_
  simp only [liabilityH2Hat, evariance_mul]
  simpa using ENNReal.Tendsto.const_mul hvarT (Or.inr ENNReal.ofReal_ne_top)

end LDSC

end MathlibExt.Biology.StatisticalGenetics.LDScoreLiability
