/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.ChiSquare
public import MathlibExt.Probability.Statistics.LikelihoodRatioTests
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# The DENTIST-S LD-consistency statistic

SLALOM (Kanai et al. 2022) flags fine-mapping loci whose association statistics are inconsistent
with a reference LD panel. Under a single causal variant `c` in a locus, the marginal `z`-score of
a variant `i` should equal `r_{ic} z_c` up to noise, and SLALOM tests this with the simplified
DENTIST statistic (DENTIST-S, after Chen et al. 2021, DENTIST)

  `T_i = (z_i - r_{ic} z_c) ^ 2 / (1 - r_{ic} ^ 2)`   (Kanai et al. 2022, Equation 1),

which the paper describes as approximately `χ²₁`. We model the pair `(z_i, z_c)` as jointly
Gaussian with unit variances, true correlation `ρ`, and means `ρ λ` and `λ` (the means implied by
a single causal variant with non-centrality `λ`; the mean of `z_i` is `ρ` times that of `z_c`),
and we evaluate the statistic with a reference correlation `r` that may differ from `ρ`.

* `map_standardized_eq_gaussianReal`: the standardized difference
  `(z_i - r z_c) / √(1 - r²)` is exactly Gaussian with mean `(ρ - r) λ / √(1 - r²)` and variance
  `(1 - 2 r ρ + r²) / (1 - r²)`, for every reference value `|r| < 1`. So `T_i` is the square
  of that Gaussian: a scaled non-central `χ²₁` in general.
* `map_dentistS_eq_chiSquare`: when the reference LD is right (`r = ρ`), `T_i` has exactly the
  `χ²₁` law, whatever `λ` is.
* `dentistVariance_eq_one_iff`, `dentistMean_eq_zero_iff`: the standardized difference has unit
  variance iff `r = 0` or `r = ρ`, and mean zero iff `r = ρ` or `λ = 0`; so for `λ ≠ 0` the
  standardized difference is standard normal iff `r = ρ`.
* The square of a standard normal variable has the `chiSquareMeasure 1` law: reuse
  `ProbabilityTheory.gaussianReal_map_sq` (no duplicate proof here).

The Gaussian model with exact unit variances is the large-sample idealization the paper's
"approximately `χ²₁`" refers to; finite-sample effects of estimating `z`-scores are not modeled.

## Main results

* `dentistS`: the DENTIST-S statistic.
* `map_standardized_eq_gaussianReal`, `map_dentistS_eq_map_sq`, `map_dentistS_eq_chiSquare`.
* `dentistVariance_eq_one_iff`, `dentistMean_eq_zero_iff`.
* `map_dentistS_eq_chiSquare` via `ProbabilityTheory.gaussianReal_map_sq`.

## References

* M. Kanai, R. Elzur, W. Zhou, Global Biobank Meta-analysis Initiative, M. J. Daly,
  H. K. Finucane, *Meta-analysis fine-mapping is often miscalibrated at single-variant
  resolution*, Cell Genomics 2 (2022), 100210.
* W. Chen, Y. Wu, Z. Zheng, T. Qi, P. M. Visscher, Z. Zhu, J. Yang, *Improved analyses of GWAS
  summary statistics by reducing data heterogeneity and errors*, Nat. Commun. 12 (2021), 7117.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace MathlibExt.Biology.StatisticalGenetics.LDOutlierTest

/-- The DENTIST-S statistic `(z_i - r z_c) ^ 2 / (1 - r ^ 2)` of a variant with `z`-score `zi`,
given the `z`-score `zc` of the lead (putative causal) variant and the reference correlation `r`
between them (Kanai et al. 2022, Equation 1). Meaningful for `r ^ 2 < 1`; for `r ^ 2 = 1` it is
`0` by the convention `x / 0 = 0`. -/
noncomputable def dentistS (r zi zc : ℝ) : ℝ := (zi - r * zc) ^ 2 / (1 - r ^ 2)

/-- The mean `(ρ - r) λ / √(1 - r²)` of the standardized DENTIST difference when the true
correlation is `ρ`, the reference correlation is `r` and the lead variant has mean `λ`. -/
noncomputable def dentistMean (ρ r lam : ℝ) : ℝ := (ρ - r) * lam / Real.sqrt (1 - r ^ 2)

/-- The variance `(1 - 2 r ρ + r²) / (1 - r²)` of the standardized DENTIST difference when the
true correlation is `ρ` and the reference correlation is `r`. -/
noncomputable def dentistVariance (ρ r : ℝ) : ℝ := (1 - 2 * r * ρ + r ^ 2) / (1 - r ^ 2)



variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Exact law of the standardized DENTIST difference.** Let `(z_i, z_c)` be jointly Gaussian
with unit variances, correlation `ρ` (the covariance, as the variances are `1`), and means
`ρ λ` and `λ`. For a reference correlation `r` with `r ^ 2 < 1`, the standardized difference
`(z_i - r z_c) / √(1 - r²)` is Gaussian with mean `dentistMean ρ r λ` and variance
`dentistVariance ρ r`. -/
theorem map_standardized_eq_gaussianReal {zi zc : Ω → ℝ}
    (hz : HasGaussianLaw (fun ω => (zi ω, zc ω)) P) {ρ r lam : ℝ}
    (hvi : Var[zi; P] = 1) (hvc : Var[zc; P] = 1) (hcov : cov[zi, zc; P] = ρ)
    (hmi : P[zi] = ρ * lam) (hmc : P[zc] = lam) (hr : r ^ 2 < 1) :
    P.map (fun ω => (zi ω - r * zc ω) / Real.sqrt (1 - r ^ 2)) =
      gaussianReal (dentistMean ρ r lam) (dentistVariance ρ r).toNNReal := by
  have hP := hz.isProbabilityMeasure
  have hs : 0 < 1 - r ^ 2 := by linarith
  set s := Real.sqrt (1 - r ^ 2) with hs_def
  have hspos : 0 < s := Real.sqrt_pos.mpr hs
  have hzi := hz.fst
  have hzc := hz.snd
  let L : ℝ × ℝ →L[ℝ] ℝ :=
    s⁻¹ • (ContinuousLinearMap.fst ℝ ℝ ℝ - r • ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hX : HasGaussianLaw (fun ω => (zi ω - r * zc ω) / s) P := by
    have h := hz.map_fun L
    convert h using 2 with ω
    simp only [L, smul_apply, sub_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    rw [div_eq_inv_mul]
  rw [hX.map_eq_gaussianReal]
  have hmi' : Integrable zi P := hzi.integrable
  have hmc' : Integrable zc P := hzc.integrable
  congr 1
  · rw [integral_div, integral_sub hmi' (hmc'.const_mul r), integral_const_mul, hmi, hmc,
      dentistMean]
    ring
  · congr 1
    have hfun : (fun ω => (zi ω - r * zc ω) / s) = fun ω => s⁻¹ * (zi ω - r * zc ω) := by
      funext ω; rw [div_eq_inv_mul]
    rw [hfun, variance_const_mul, variance_fun_sub hzi.memLp_two (hzc.memLp_two.const_mul r),
      covariance_const_mul_right, variance_const_mul, hvi, hvc, hcov, inv_pow,
      Real.sq_sqrt hs.le, dentistVariance]
    field_simp


/-- When the reference correlation equals the true correlation `ρ` (`ρ ^ 2 < 1`), the DENTIST-S
statistic has the law of the square of a standard normal variable. -/
theorem map_dentistS_eq_map_sq {zi zc : Ω → ℝ}
    (hz : HasGaussianLaw (fun ω => (zi ω, zc ω)) P) {ρ lam : ℝ}
    (hvi : Var[zi; P] = 1) (hvc : Var[zc; P] = 1) (hcov : cov[zi, zc; P] = ρ)
    (hmi : P[zi] = ρ * lam) (hmc : P[zc] = lam) (hρ : ρ ^ 2 < 1) :
    P.map (fun ω => dentistS ρ (zi ω) (zc ω)) = (gaussianReal 0 1).map (fun x : ℝ => x ^ 2) := by
  have hP := hz.isProbabilityMeasure
  have hs : 0 < 1 - ρ ^ 2 := by linarith
  have h := map_standardized_eq_gaussianReal hz hvi hvc hcov hmi hmc hρ
  have hv : dentistVariance ρ ρ = 1 := by
    rw [dentistVariance]; field_simp; ring
  have hm : dentistMean ρ ρ lam = 0 := by simp [dentistMean]
  rw [hv, hm, Real.toNNReal_one] at h
  have hf : AEMeasurable (fun ω => (zi ω - ρ * zc ω) / Real.sqrt (1 - ρ ^ 2)) P :=
    (hz.fst.aemeasurable.sub (hz.snd.aemeasurable.const_mul ρ)).div_const _
  rw [← h, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hf]
  congr 1
  funext ω
  simp only [Function.comp, dentistS, div_pow, Real.sq_sqrt hs.le]


/-- **DENTIST-S is exactly `χ²₁` when the reference LD is right.** Under the model of
`map_standardized_eq_gaussianReal` with reference correlation equal to the true correlation
`ρ` (`ρ ^ 2 < 1`), the DENTIST-S statistic has the `chiSquareMeasure 1` law, for every value
`λ` of the lead variant's mean. -/
theorem map_dentistS_eq_chiSquare {zi zc : Ω → ℝ}
    (hz : HasGaussianLaw (fun ω => (zi ω, zc ω)) P) {ρ lam : ℝ}
    (hvi : Var[zi; P] = 1) (hvc : Var[zc; P] = 1) (hcov : cov[zi, zc; P] = ρ)
    (hmi : P[zi] = ρ * lam) (hmc : P[zc] = lam) (hρ : ρ ^ 2 < 1) :
    P.map (fun ω => dentistS ρ (zi ω) (zc ω)) = chiSquareMeasure 1 := by
  rw [map_dentistS_eq_map_sq hz hvi hvc hcov hmi hmc hρ, ProbabilityTheory.gaussianReal_map_sq]

/-- The standardized DENTIST difference has unit variance iff the reference correlation is `0`
or equals the true correlation (for `r ^ 2 < 1`). -/
theorem dentistVariance_eq_one_iff {ρ r : ℝ} (hr : r ^ 2 < 1) :
    dentistVariance ρ r = 1 ↔ r = 0 ∨ r = ρ := by
  have h : 1 - r ^ 2 ≠ 0 := by linarith
  rw [dentistVariance, div_eq_one_iff_eq h]
  constructor
  · intro heq
    have : r * (r - ρ) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  · rintro (h0 | h0) <;> subst h0 <;> ring

/-- The standardized DENTIST difference has mean zero iff the reference correlation equals the
true correlation or the lead variant has mean zero (for `r ^ 2 < 1`). -/
theorem dentistMean_eq_zero_iff {ρ r lam : ℝ} (hr : r ^ 2 < 1) :
    dentistMean ρ r lam = 0 ↔ r = ρ ∨ lam = 0 := by
  have h : Real.sqrt (1 - r ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  rw [dentistMean, div_eq_zero_iff, or_iff_left h, mul_eq_zero, sub_eq_zero, eq_comm]

end MathlibExt.Biology.StatisticalGenetics.LDOutlierTest
