/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScore
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Genomic prediction from summary statistics

Exact finite identities behind polygenic-score accuracy, joint and conditional analysis from
summary statistics, extensions of LD-score regression, and the trend test for association.

## Main results

* `PRSModel.accuracySq_eq`: **polygenic-score accuracy** (Daetwyler, Villanueva & Woolliams
  2008; Dudbridge 2013). Effects `β k` with `𝔼[β βᵀ] = (h² / M) I`, estimates `β̂ = β + e` with
  `𝔼[e eᵀ] = s² I` and `𝔼[β eᵀ] = 0`. In a target population of standardized, uncorrelated
  markers (`integral_score_mul_score`) the covariance of the genetic value `g = xᵀ β` and the
  score `ĝ = xᵀ β̂` is `βᵀ β̂`, and the variances are `βᵀ β` and `β̂ᵀ β̂`. The squared correlation
  as a **ratio of expectations**, `𝔼[βᵀβ̂]² / (𝔼[βᵀβ] 𝔼[β̂ᵀβ̂])`, is `h² / (h² + M s²)`;
  with the sampling variance `s² = 1 / N` of the cited papers it is `N h² / (N h² + M)`
  (`PRSModel.accuracySq_eq_of_s2`). This is not the expectation of the squared sample
  correlation.
* `PRSModel.ofLDScore`, `PRSModel.accuracySq_ofLDScore`: the same quantity when the effects are
  estimated by `β̂ = Xᵀ y / N` in the LD-score model with orthogonal standardized training
  columns (`HasOrthogonalColumns`): there `s² = (1 - h²) / N` exactly, and the accuracy is
  `N h² / (N h² + M (1 - h²))`. The cited formula takes the residual variance to be `1`.
* `transpose_mulVec_eq_gramDiag_mulVec`, `cojo_joint`, `conditionalEstimate_eq_summary`,
  `conditionalEstimate_eq_residual`: **COJO algebraic formulas** (Yang et al. 2012). With the
  marginal estimates `β̂_j = x_jᵀ y / x_jᵀ x_j` and `D = diag(XᵀX)`, `Xᵀ y = D β̂`, giving the
  displayed joint and conditional formulas in terms of summary statistics. They have their
  usual least-squares interpretation when the relevant Gram determinants are units. Without
  that hypothesis Mathlib's nonsingular inverse is zero on a singular Gram matrix, so these
  unconditional equalities can return junk values rather than least-squares fits.
* `StratifiedModel.integral_chiSq_of_standardized`: **stratified LD-score regression**
  (Finucane et al. 2015): if `Var β_k = ∑_C τ_C [k ∈ C]`, then
  `𝔼[χ²_j] = N ∑_C τ_C ℓ(j, C) + σ²_e` for a standardized marker `j`;
  `StratifiedModel.integral_chiSq_single_causal`: one causal variant `c` gives
  `𝔼[χ²_m] = N τ r²_mc + σ²_e` (the LD-proxy noncentrality).
* `CrossTraitModel.integral_z_mul_z`: an exact **cross-trait scaled-score identity** motivated by
  Bulik-Sullivan et al. 2015b. Its overlap term uses the residual cross-moment `ρ_e`; the model
  does not identify this parameter with phenotypic correlation or require within-trait moments
  that would make the scaled scores standardized z-scores.
* `ArmitageTrend.trendStat_eq_total_mul_corrSq`: the **Cochran–Armitage trend statistic** is
  `N r²` (Armitage 1955); `ArmitageTrend.allelicStat_mul_hweVar`,
  `ArmitageTrend.allelicStat_eq_trendStat_iff`: the allelic test times `2 p q` is the trend
  test times the observed genotype-score variance, so the two agree iff the pooled sample is in
  Hardy–Weinberg proportions (Sasieni 1997).

## References

* H. D. Daetwyler, B. Villanueva, J. A. Woolliams, *Accuracy of predicting the genetic risk of
  disease using a genome-wide approach*, PLoS ONE 3 (2008), e3395.
* F. Dudbridge, *Power and predictive accuracy of polygenic risk scores*, PLoS Genet. 9 (2013),
  e1003348.
* J. Yang et al., *Conditional and joint multiple-SNP analysis of GWAS summary statistics
  identifies additional variants influencing complex traits*, Nat. Genet. 44 (2012), 369–375.
* B. Bulik-Sullivan et al., *An atlas of genetic correlations across human diseases and
  traits*, Nat. Genet. 47 (2015), 1236–1241.
* H. K. Finucane et al., *Partitioning heritability by functional annotation using genome-wide
  association summary statistics*, Nat. Genet. 47 (2015), 1228–1235.
* J. K. Pritchard, M. Przeworski, *Linkage disequilibrium in humans: models and data*,
  Am. J. Hum. Genet. 69 (2001), 1–14.
* P. Armitage, *Tests for linear trends in proportions and frequencies*, Biometrics 11 (1955),
  375–386.
* P. D. Sasieni, *From genotypes to genes: doubling the sample size*, Biometrics 53 (1997),
  1253–1261.
-/

@[expose] public section

open MeasureTheory Matrix

namespace MathlibExt.Biology.StatisticalGenetics.GenomicPrediction

open LDScore

section Moments

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

private theorem integral_sum_mul_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → Ω → ℝ) (g : κ → Ω → ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : ∀ l, MemLp (g l) 2 μ) :
    ∫ ω, (∑ k, a k * f k ω) * (∑ l, b l * g l ω) ∂μ =
      ∑ k, ∑ l, a k * b l * ∫ ω, f k ω * g l ω ∂μ := by
  have hp (k : ι) (l : κ) : Integrable (fun ω => a k * b l * (f k ω * g l ω)) μ :=
    ((hf k).integrable_mul (hg l)).const_mul _
  have he (ω : Ω) : (∑ k, a k * f k ω) * (∑ l, b l * g l ω) =
      ∑ k, ∑ l, a k * b l * (f k ω * g l ω) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun k _ =>
    integrable_finsetSum Finset.univ (fun l _ => hp k l))]
  simp_rw [integral_finsetSum Finset.univ (fun l _ => hp _ l), integral_const_mul]

end Moments

/-! ### Polygenic-score accuracy -/

section PRS

variable {Ω : Type*} {m : MeasurableSpace Ω} {M : ℕ}

/-- In a target population whose marker genotypes `x j` have raw second moments
`∫ x j * x k = [j = k]` (standardized, uncorrelated markers), the scores `xᵀ a` and `xᵀ b` of two
effect vectors have raw cross moment `aᵀ b`. With mean-zero genotypes and a probability measure
this is the covariance of the genetic value `xᵀ β` and the polygenic score `xᵀ β̂`. -/
theorem integral_score_mul_score {Ξ : Type*} {mΞ : MeasurableSpace Ξ} {ν : Measure Ξ}
    (x : Fin M → Ξ → ℝ) (hx : ∀ j, MemLp (x j) 2 ν)
    (hxx : ∀ j k, ∫ ξ, x j ξ * x k ξ ∂ν = if j = k then 1 else 0) (a b : Fin M → ℝ) :
    ∫ ξ, (∑ j, a j * x j ξ) * (∑ k, b k * x k ξ) ∂ν = ∑ j, a j * b j := by
  rw [integral_sum_mul_sum x x a b hx hx]
  simp [hxx]

/-- The effect-estimate model behind polygenic-score accuracy (Daetwyler et al. 2008;
Dudbridge 2013), at the level of raw second moments, for `M` independent markers: true effects
`beta k` with `∫ β k β l = (h² / M) [k = l]`, estimation errors `err k` with
`∫ e k e l = s² [k = l]`, orthogonal to the effects. The estimates are `β̂ = β + e`
(`betaHat`). For a probability measure and mean-zero effects and errors these are the
covariance conditions of the cited model; `s²` is the sampling variance of each estimate
(`1 / N` in the cited papers, `(1 - h²) / N` in `ofLDScore`). -/
structure PRSModel (μ : Measure Ω) (M : ℕ) where
  /-- The SNP heritability `h²`. -/
  h2 : ℝ
  /-- The sampling variance `s²` of each effect estimate. -/
  s2 : ℝ
  /-- Random per-marker effects. -/
  beta : Fin M → Ω → ℝ
  /-- Random estimation errors. -/
  err : Fin M → Ω → ℝ
  /-- Effects are square integrable. -/
  memLp_beta : ∀ k, MemLp (beta k) 2 μ
  /-- Errors are square integrable. -/
  memLp_err : ∀ k, MemLp (err k) 2 μ
  /-- `∫ β βᵀ = (h² / M) I`. -/
  integral_beta_mul : ∀ k l, ∫ ω, beta k ω * beta l ω ∂μ = if k = l then h2 / M else 0
  /-- `∫ e eᵀ = s² I`. -/
  integral_err_mul : ∀ k l, ∫ ω, err k ω * err l ω ∂μ = if k = l then s2 else 0
  /-- Effects and errors are orthogonal: `∫ β eᵀ = 0`. -/
  integral_beta_mul_err : ∀ k l, ∫ ω, beta k ω * err l ω ∂μ = 0

namespace PRSModel

variable {μ : Measure Ω} (D : PRSModel μ M)

/-- The model forces `h² ≥ 0` when there is at least one marker. -/
theorem h2_nonneg (hM : 0 < M) : 0 ≤ D.h2 := by
  have h := D.integral_beta_mul ⟨0, hM⟩ ⟨0, hM⟩
  rw [ite_eq_left rfl] at h
  have h0 : 0 ≤ ∫ ω, D.beta ⟨0, hM⟩ ω * D.beta ⟨0, hM⟩ ω ∂μ :=
    integral_nonneg fun ω => mul_self_nonneg _
  rw [h] at h0
  exact (div_nonneg_iff.1 h0).elim (fun h => h.1) fun h =>
    absurd h.2 (not_le.2 (Nat.cast_pos.2 hM))

/-- The model forces `s² ≥ 0` when there is at least one marker. -/
theorem s2_nonneg (hM : 0 < M) : 0 ≤ D.s2 := by
  have h := D.integral_err_mul ⟨0, hM⟩ ⟨0, hM⟩
  rw [ite_eq_left rfl] at h
  rw [← h]
  exact integral_nonneg fun ω => mul_self_nonneg _

/-- The estimated effects `β̂ = β + e`. -/
def betaHat (k : Fin M) (ω : Ω) : ℝ := D.beta k ω + D.err k ω

/-- The squared correlation of the genetic value and the polygenic score as a ratio of
expectations, `𝔼[βᵀβ̂]² / (𝔼[βᵀβ] 𝔼[β̂ᵀβ̂])`: by `integral_score_mul_score`, `βᵀβ̂`, `βᵀβ` and
`β̂ᵀβ̂` are the covariance and variances of `xᵀβ` and `xᵀβ̂` over a target population of
standardized uncorrelated markers. It is not the expectation of a squared correlation. -/
noncomputable def accuracySq : ℝ :=
  (∫ ω, ∑ k, D.beta k ω * D.betaHat k ω ∂μ) ^ 2 /
    ((∫ ω, ∑ k, D.beta k ω ^ 2 ∂μ) * ∫ ω, ∑ k, D.betaHat k ω ^ 2 ∂μ)

/-- `𝔼[βᵀβ̂] = h²` (for at least one marker). -/
theorem integral_beta_mul_betaHat (hM : M ≠ 0) :
    ∫ ω, ∑ k, D.beta k ω * D.betaHat k ω ∂μ = D.h2 := by
  have hi (k : Fin M) : Integrable (fun ω => D.beta k ω * D.beta k ω) μ :=
    (D.memLp_beta k).integrable_mul (D.memLp_beta k)
  have hj (k : Fin M) : Integrable (fun ω => D.beta k ω * D.err k ω) μ :=
    (D.memLp_beta k).integrable_mul (D.memLp_err k)
  have hk (k : Fin M) : ∫ ω, (D.beta k ω * D.beta k ω + D.beta k ω * D.err k ω) ∂μ =
      D.h2 / M := by
    rw [integral_add (hi k) (hj k), D.integral_beta_mul, D.integral_beta_mul_err]
    simp
  have hs (k : Fin M) : Integrable (fun ω => D.beta k ω * D.beta k ω +
      D.beta k ω * D.err k ω) μ := (hi k).add (hj k)
  simp only [betaHat, mul_add]
  rw [integral_finsetSum _ fun k _ => hs k]
  simp_rw [hk]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- `𝔼[βᵀβ] = h²` (for at least one marker). -/
theorem integral_beta_sq (hM : M ≠ 0) : ∫ ω, ∑ k, D.beta k ω ^ 2 ∂μ = D.h2 := by
  have hs (k : Fin M) : Integrable (fun ω => D.beta k ω * D.beta k ω) μ :=
    (D.memLp_beta k).integrable_mul (D.memLp_beta k)
  simp_rw [sq]
  rw [integral_finsetSum _ fun k _ => hs k]
  simp only [D.integral_beta_mul, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- `𝔼[β̂ᵀβ̂] = h² + M s²` (for at least one marker). -/
theorem integral_betaHat_sq (hM : M ≠ 0) :
    ∫ ω, ∑ k, D.betaHat k ω ^ 2 ∂μ = D.h2 + M * D.s2 := by
  have hi (k : Fin M) : Integrable (fun ω => D.beta k ω * D.beta k ω) μ :=
    (D.memLp_beta k).integrable_mul (D.memLp_beta k)
  have hj (k : Fin M) : Integrable (fun ω => 2 * (D.beta k ω * D.err k ω)) μ :=
    ((D.memLp_beta k).integrable_mul (D.memLp_err k)).const_mul 2
  have hl (k : Fin M) : Integrable (fun ω => D.err k ω * D.err k ω) μ :=
    (D.memLp_err k).integrable_mul (D.memLp_err k)
  have he (ω : Ω) : ∑ k, D.betaHat k ω ^ 2 =
      ∑ k, (D.beta k ω * D.beta k ω + 2 * (D.beta k ω * D.err k ω) +
        D.err k ω * D.err k ω) :=
    Finset.sum_congr rfl fun k _ => by simp only [betaHat]; ring
  have hk (k : Fin M) : ∫ ω, (D.beta k ω * D.beta k ω + 2 * (D.beta k ω * D.err k ω) +
      D.err k ω * D.err k ω) ∂μ = D.h2 / M + D.s2 := by
    have hij : Integrable (fun ω => D.beta k ω * D.beta k ω +
        2 * (D.beta k ω * D.err k ω)) μ := (hi k).add (hj k)
    rw [integral_add hij (hl k), integral_add (hi k) (hj k),
      integral_const_mul, D.integral_beta_mul, D.integral_beta_mul_err, D.integral_err_mul]
    simp
  have hs (k : Fin M) : Integrable (fun ω => D.beta k ω * D.beta k ω +
      2 * (D.beta k ω * D.err k ω) + D.err k ω * D.err k ω) μ := ((hi k).add (hj k)).add (hl k)
  simp_rw [he]
  rw [integral_finsetSum _ fun k _ => hs k]
  simp_rw [hk]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Polygenic-score accuracy** as a ratio of expectations: `r²_g = h² / (h² + M s²)`. (If
`h² = 0` both sides are `0`.) -/
theorem accuracySq_eq (hM : M ≠ 0) : D.accuracySq = D.h2 / (D.h2 + M * D.s2) := by
  rw [accuracySq, D.integral_beta_mul_betaHat hM, D.integral_beta_sq hM,
    D.integral_betaHat_sq hM]
  rcases eq_or_ne D.h2 0 with h | h
  · simp [h]
  · rw [sq, mul_div_mul_left _ _ h]

/-- **Daetwyler–Dudbridge formula**: with sampling variance `s² = 1 / N`,
`r²_g = N h² / (N h² + M)`. -/
theorem accuracySq_eq_of_s2 {N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hs : D.s2 = 1 / N) :
    D.accuracySq = N * D.h2 / (N * D.h2 + M) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [D.accuracySq_eq hM, hs, ← mul_div_mul_left _ _ hN']
  congr 1
  field_simp

end PRSModel

/-- The training genotype matrix has orthogonal columns with sum of squares `N`,
`∑ i, X i k * X i l = N [k = l]`; for centered columns this says that the markers are
uncorrelated, with unit sample variance, in the training sample. -/
def HasOrthogonalColumns {N : ℕ} (X : Matrix (Fin N) (Fin M) ℝ) : Prop :=
  ∀ k l, ∑ i, X i k * X i l = if k = l then (N : ℝ) else 0

namespace PRSModel

variable {N : ℕ} {μ : Measure Ω}

/-- The effect-estimate model obtained from the LD-score model when the effects are estimated by
the normalized scores `β̂ = Xᵀ y / N` on a training matrix with orthogonal standardized columns:
the error is `e k = ∑ i, X i k ε i / N` and its sampling variance is `(1 - h²) / N`. -/
noncomputable def ofLDScore (D : LDScore.Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ)
    (hX : HasOrthogonalColumns X) : PRSModel μ M where
  h2 := D.h2
  s2 := (1 - D.h2) / N
  beta := D.beta
  err k ω := ∑ i, X i k / N * D.eps i ω
  memLp_beta := D.memLp_beta
  memLp_err k := by
    have h := memLp_finsetSum Finset.univ fun i _ => (D.memLp_eps i).const_mul (X i k / N)
    convert h using 1
  integral_beta_mul := D.integral_beta_mul
  integral_err_mul k l := by
    rw [integral_sum_mul_sum _ _ _ _ D.memLp_eps D.memLp_eps]
    simp_rw [D.integral_eps_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    have h : ∑ i, X i k / N * (X i l / N) * (1 - D.h2) =
        (∑ i, X i k * X i l) * ((1 - D.h2) / N ^ 2) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h, hX k l]
    rcases eq_or_ne (N : ℝ) 0 with hN | hN
    · simp [hN]
    · split_ifs
      · field_simp
      · simp
  integral_beta_mul_err k l := by
    have h (i : Fin N) : ∫ ω, D.beta k ω * (X i l / N * D.eps i ω) ∂μ = 0 := by
      have he : (fun ω => D.beta k ω * (X i l / N * D.eps i ω)) =
          fun ω => X i l / N * (D.beta k ω * D.eps i ω) := funext fun ω => by ring
      rw [he, integral_const_mul, D.integral_beta_mul_eps, mul_zero]
    have hi (i : Fin N) : Integrable (fun ω => D.beta k ω * (X i l / N * D.eps i ω)) μ :=
      (D.memLp_beta k).integrable_mul ((D.memLp_eps i).const_mul (X i l / N))
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun i _ => hi i]
    simp [h]

/-- The estimates of `ofLDScore` are the normalized scores `Xᵀ y / N` of the LD-score model. -/
theorem ofLDScore_betaHat (D : LDScore.Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ)
    (hX : HasOrthogonalColumns X) (hN : N ≠ 0) (k : Fin M) (ω : Ω) :
    (ofLDScore D X hX).betaHat k ω = D.betaHat X k ω := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have h1 : ∑ i, X i k * ∑ l, X i l * D.beta l ω = N * D.beta k ω := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hX k, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
  change D.beta k ω + ∑ i, X i k / N * D.eps i ω = _
  simp only [LDScore.Model.betaHat, LDScore.Model.pheno, mul_add, Finset.sum_add_distrib, h1,
    add_div, Finset.sum_div]
  rw [mul_div_cancel_left₀ _ hN']
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Polygenic-score accuracy in the LD-score model**: with orthogonal standardized training
columns, `β̂ = Xᵀ y / N` and residual variance `1 - h²`,
`r²_g = N h² / (N h² + M (1 - h²))`. The cited `N h² / (N h² + M)` takes the residual variance to
be `1`. -/
theorem accuracySq_ofLDScore (D : LDScore.Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ)
    (hX : HasOrthogonalColumns X) (hN : N ≠ 0) (hM : M ≠ 0) :
    (ofLDScore D X hX).accuracySq = N * D.h2 / (N * D.h2 + M * (1 - D.h2)) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [accuracySq_eq _ hM, ← mul_div_mul_left _ _ hN']
  change N * D.h2 / (N * (D.h2 + M * ((1 - D.h2) / N))) = _
  congr 1
  field_simp

end PRSModel

end PRS

/-! ### COJO: joint and conditional estimates from marginal statistics -/

section COJO

variable {n : ℕ} {ι ι₁ ι₂ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι₁] [DecidableEq ι₁]
  [Fintype ι₂] [DecidableEq ι₂]

/-- The marginal least-squares estimate `x_jᵀ y / x_jᵀ x_j` of marker `j` (single-marker
regression without intercept, on centered genotypes and phenotype as in Yang et al. 2012). -/
noncomputable def marginalEstimate (X : Matrix (Fin n) ι ℝ) (y : Fin n → ℝ) (j : ι) : ℝ :=
  (Xᵀ *ᵥ y) j / (Xᵀ * X) j j

/-- The diagonal `D = diag(XᵀX)` of the Gram matrix. -/
noncomputable def gramDiag (X : Matrix (Fin n) ι ℝ) : Matrix ι ι ℝ :=
  diagonal fun j => (Xᵀ * X) j j

/-- `Xᵀ y = D β̂` for the marginal estimates `β̂` (Yang et al. 2012). This holds for every
genotype matrix: a column with `x_jᵀ x_j = 0` is zero, so both sides vanish there. -/
theorem transpose_mulVec_eq_gramDiag_mulVec (X : Matrix (Fin n) ι ℝ) (y : Fin n → ℝ) :
    Xᵀ *ᵥ y = gramDiag X *ᵥ marginalEstimate X y := by
  ext j
  rw [gramDiag, mulVec_diagonal, marginalEstimate]
  rcases eq_or_ne ((Xᵀ * X) j j) 0 with h | h
  · have hsum : ∑ i, X i j * X i j = 0 := by simpa [mul_apply] using h
    have hcol : ∀ i, X i j = 0 := fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (X i j))).1 hsum i
        (Finset.mem_univ _)
      exact mul_self_eq_zero.1 this
    simp [mulVec, dotProduct, hcol]
  · field_simp

/-- **COJO joint estimate** (Yang et al. 2012, eq. (5)): the joint least-squares estimate
`(XᵀX)⁻¹ Xᵀ y` equals `(XᵀX)⁻¹ D β̂` in terms of the marginal estimates `β̂`, so it can be
computed from summary statistics and `XᵀX`. (Stated for every `X`; it is the least-squares
estimate when `XᵀX` is invertible.) -/
theorem cojo_joint (X : Matrix (Fin n) ι ℝ) (y : Fin n → ℝ) :
    (Xᵀ * X)⁻¹ *ᵥ (Xᵀ *ᵥ y) = (Xᵀ * X)⁻¹ *ᵥ (gramDiag X *ᵥ marginalEstimate X y) := by
  rw [transpose_mulVec_eq_gramDiag_mulVec]

/-- For markers uncorrelated in the sample (`XᵀX` diagonal) without zero columns, the joint
estimate is the vector of marginal estimates. -/
theorem cojo_joint_of_diagonal (X : Matrix (Fin n) ι ℝ) (y : Fin n → ℝ)
    (hX : Xᵀ * X = gramDiag X) (hD : ∀ j, (Xᵀ * X) j j ≠ 0) :
    (Xᵀ * X)⁻¹ *ᵥ (Xᵀ *ᵥ y) = marginalEstimate X y := by
  have hdet : IsUnit (gramDiag X).det := by
    rw [gramDiag, det_diagonal]
    exact (Finset.prod_ne_zero_iff.mpr fun j _ => hD j).isUnit
  rw [cojo_joint, hX, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]

/-- The unconditional algebraic formula from Yang et al. 2012, eq. (15):
`(X₂ᵀX₂)⁻¹ X₂ᵀ y - (X₂ᵀX₂)⁻¹ X₂ᵀX₁ (X₁ᵀX₁)⁻¹ X₁ᵀ y`. When both Gram determinants are units,
this has the usual interpretation as the block-2 fit conditional on the block-1 fit. For a
singular Gram matrix, Mathlib's nonsingular inverse is zero and the value can be a junk value. -/
noncomputable def conditionalEstimate (X₁ : Matrix (Fin n) ι₁ ℝ) (X₂ : Matrix (Fin n) ι₂ ℝ)
    (y : Fin n → ℝ) : ι₂ → ℝ :=
  (X₂ᵀ * X₂)⁻¹ *ᵥ (X₂ᵀ *ᵥ y) - ((X₂ᵀ * X₂)⁻¹ * X₂ᵀ * X₁ * (X₁ᵀ * X₁)⁻¹) *ᵥ (X₁ᵀ *ᵥ y)

/-- **COJO conditional algebraic formula from summary statistics** (Yang et al. 2012, eq. (17)):
`b̂₂|b̂₁ = (X₂ᵀX₂)⁻¹ D₂ β̂₂ - (X₂ᵀX₂)⁻¹ X₂ᵀX₁ (X₁ᵀX₁)⁻¹ D₁ β̂₁`. -/
theorem conditionalEstimate_eq_summary (X₁ : Matrix (Fin n) ι₁ ℝ) (X₂ : Matrix (Fin n) ι₂ ℝ)
    (y : Fin n → ℝ) :
    conditionalEstimate X₁ X₂ y =
      (X₂ᵀ * X₂)⁻¹ *ᵥ (gramDiag X₂ *ᵥ marginalEstimate X₂ y) -
        ((X₂ᵀ * X₂)⁻¹ * X₂ᵀ * X₁ * (X₁ᵀ * X₁)⁻¹) *ᵥ (gramDiag X₁ *ᵥ marginalEstimate X₁ y) := by
  rw [conditionalEstimate, transpose_mulVec_eq_gramDiag_mulVec X₂,
    transpose_mulVec_eq_gramDiag_mulVec X₁]

/-- Unconditionally, the conditional formula equals the nonsingular-inverse formula applied to
the algebraic residual `y - X₁ ((X₁ᵀX₁)⁻¹ X₁ᵀ y)`. If both Gram determinants are units, these
are the successive least-squares fits on blocks 1 and 2. With a singular Gram matrix they need
not minimize residual error. This is in general not the block-2 part of the joint formula on
both blocks (the formulas agree when `X₂ᵀX₁ = 0`). -/
theorem conditionalEstimate_eq_residual (X₁ : Matrix (Fin n) ι₁ ℝ) (X₂ : Matrix (Fin n) ι₂ ℝ)
    (y : Fin n → ℝ) :
    conditionalEstimate X₁ X₂ y =
      (X₂ᵀ * X₂)⁻¹ *ᵥ (X₂ᵀ *ᵥ (y - X₁ *ᵥ ((X₁ᵀ * X₁)⁻¹ *ᵥ (X₁ᵀ *ᵥ y)))) := by
  simp only [conditionalEstimate, mulVec_sub, mulVec_mulVec, Matrix.mul_assoc]

end COJO

/-! ### Stratified and cross-trait LD-score regression -/

section Stratified

variable {Ω : Type*} {m : MeasurableSpace Ω} {N M : ℕ}

/-- The stratified LD score `ℓ(j, C) = ∑_{k ∈ C} r j k ²` of marker `j` with respect to the
annotation category `C` (Finucane et al. 2015). -/
noncomputable def stratLDScore (X : Matrix (Fin N) (Fin M) ℝ) (C : Finset (Fin M)) (j : Fin M) :
    ℝ :=
  ∑ k ∈ C, ldCorr X j k ^ 2

/-- The stratified LD-score model (Finucane et al. 2015), at the level of raw second moments:
annotation categories `cat c ⊆ {markers}` (possibly overlapping), per-category contributions
`tau c`, effects with `∫ β k β l = [k = l] ∑_c τ_c [k ∈ cat c]`, noise with
`∫ ε i ε i' = σ²_e [i = i']`, effects orthogonal to noise. The cited model normalizes the
phenotypic variance so that `σ²_e ≈ 1`; the confounding term `N a` is not modeled. -/
structure StratifiedModel (μ : Measure Ω) (N M : ℕ) (C : Type*) [Fintype C] where
  /-- The markers in each annotation category. -/
  cat : C → Finset (Fin M)
  /-- The per-marker heritability contribution `τ_C` of each category. -/
  tau : C → ℝ
  /-- The noise variance `σ²_e`. -/
  sigma2e : ℝ
  /-- Random per-marker effects. -/
  beta : Fin M → Ω → ℝ
  /-- Random environmental noise. -/
  eps : Fin N → Ω → ℝ
  /-- Effects are square integrable. -/
  memLp_beta : ∀ k, MemLp (beta k) 2 μ
  /-- Noise terms are square integrable. -/
  memLp_eps : ∀ i, MemLp (eps i) 2 μ
  /-- `∫ β k β l = [k = l] ∑_c τ_c [k ∈ cat c]`. -/
  integral_beta_mul : ∀ k l, ∫ ω, beta k ω * beta l ω ∂μ =
    if k = l then ∑ c, (if k ∈ cat c then tau c else 0) else 0
  /-- `∫ ε εᵀ = σ²_e I`. -/
  integral_eps_mul : ∀ i i', ∫ ω, eps i ω * eps i' ω ∂μ = if i = i' then sigma2e else 0
  /-- Effects and noise are orthogonal. -/
  integral_beta_mul_eps : ∀ k i, ∫ ω, beta k ω * eps i ω ∂μ = 0

namespace StratifiedModel

variable {C : Type*} [Fintype C] {μ : Measure Ω} (D : StratifiedModel μ N M C)
  (X : Matrix (Fin N) (Fin M) ℝ)

/-- The phenotype `y = X β + ε`. -/
def pheno (i : Fin N) (ω : Ω) : ℝ := ∑ k, X i k * D.beta k ω + D.eps i ω

/-- The `N`-normalized score `β̂ j = X_jᵀ y / N`. -/
noncomputable def betaHat (j : Fin M) (ω : Ω) : ℝ := (∑ i, X i j * D.pheno X i ω) / N

/-- The association statistic `χ² j = N β̂ j ²`. -/
noncomputable def chiSq (j : Fin M) (ω : Ω) : ℝ := N * D.betaHat X j ω ^ 2

private theorem betaHat_eq_sum (j : Fin M) (ω : Ω) :
    D.betaHat X j ω = ∑ k, ldCorr X j k * D.beta k ω + ∑ i, (X i j / N) * D.eps i ω := by
  unfold betaHat pheno ldCorr
  simp_rw [mul_add, Finset.sum_add_distrib, add_div, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, div_mul_eq_mul_div, Finset.sum_div]

/-- The exact expectation of the association statistic in the stratified model, for any
genotype matrix: `𝔼[χ² j] = N ∑_c τ_c ℓ(j, cat c) + σ²_e (∑ i, X i j ²) / N`. -/
theorem integral_chiSq (j : Fin M) :
    ∫ ω, D.chiSq X j ω ∂μ =
      N * ∑ c, D.tau c * stratLDScore X (D.cat c) j + D.sigma2e * (∑ i, X i j ^ 2) / N := by
  classical
  by_cases hN : N = 0
  · subst hN
    simp [chiSq]
  let f : Fin M ⊕ Fin N → Ω → ℝ := Sum.elim D.beta D.eps
  let a : Fin M ⊕ Fin N → ℝ := Sum.elim (ldCorr X j) (fun i => X i j / N)
  have hf (u : Fin M ⊕ Fin N) : MemLp (f u) 2 μ := by
    cases u with
    | inl k => exact D.memLp_beta k
    | inr i => exact D.memLp_eps i
  have hb (ω : Ω) : D.betaHat X j ω = ∑ u, a u * f u ω := by
    rw [betaHat_eq_sum, Fintype.sum_sum_type]
    rfl
  have hc (i : Fin N) (k : Fin M) : ∫ ω, D.eps i ω * D.beta k ω ∂μ = 0 := by
    rw [← D.integral_beta_mul_eps k i]
    congr 1
    ext ω
    ring
  have hsq : ∫ ω, D.betaHat X j ω ^ 2 ∂μ =
      ∑ k, ldCorr X j k ^ 2 * (∑ c, if k ∈ D.cat c then D.tau c else 0) +
        ∑ i, (X i j / N) ^ 2 * D.sigma2e := by
    simp_rw [hb, sq]
    rw [integral_sum_mul_sum f f a a hf hf]
    simp [Fintype.sum_sum_type, f, a, D.integral_beta_mul, D.integral_eps_mul,
      D.integral_beta_mul_eps, hc]
  have hstrat : ∑ k, ldCorr X j k ^ 2 * (∑ c, if k ∈ D.cat c then D.tau c else 0) =
      ∑ c, D.tau c * stratLDScore X (D.cat c) j := by
    simp_rw [Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_ite_mem, Finset.univ_inter, stratLDScore, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [chiSq]
  rw [integral_const_mul, hsq, hstrat]
  simp_rw [div_pow, ← Finset.sum_mul, ← Finset.sum_div]
  field_simp

/-- **Stratified LD-score regression** (Finucane et al. 2015): for a marker column with sum of
squares `N ≠ 0`, `𝔼[χ² j] = N ∑_c τ_c ℓ(j, cat c) + σ²_e`. -/
theorem integral_chiSq_of_standardized (hN : N ≠ 0) (j : Fin M) (hj : ∑ i, X i j ^ 2 = N) :
    ∫ ω, D.chiSq X j ω ∂μ = N * ∑ c, D.tau c * stratLDScore X (D.cat c) j + D.sigma2e := by
  rw [D.integral_chiSq X j, hj, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr hN)]

/-- **One causal variant** (the LD-proxy noncentrality; Pritchard & Przeworski 2001): if the
only category is the single causal marker `c` with variance `τ`, then for a marker `m` with sum
of squares `N ≠ 0`, `𝔼[χ² m] = N τ r m c ² + σ²_e`. -/
theorem integral_chiSq_single_causal (D : StratifiedModel μ N M Unit) (c : Fin M)
    (hcat : D.cat () = {c}) (hN : N ≠ 0) (j : Fin M) (hj : ∑ i, X i j ^ 2 = N) :
    ∫ ω, D.chiSq X j ω ∂μ = N * D.tau () * ldCorr X j c ^ 2 + D.sigma2e := by
  rw [D.integral_chiSq_of_standardized X hN j hj]
  simp [stratLDScore, hcat, mul_assoc]

end StratifiedModel

end Stratified

section CrossTrait

variable {Ω : Type*} {m : MeasurableSpace Ω} {n M : ℕ}

/-- The in-sample normalized cross product `∑_{i ∈ S} X i j X i k / |S|` of markers `j`, `k` in
the sample `S` of a pool of individuals (the sample LD correlation for a matrix standardized
within `S`). -/
noncomputable def sampleCorr (X : Matrix (Fin n) (Fin M) ℝ) (S : Finset (Fin n)) (j k : Fin M) :
    ℝ :=
  (∑ i ∈ S, X i j * X i k) / S.card

/-- The bivariate LD-score model (Bulik-Sullivan et al. 2015b), at the level of the cross
second moments that enter `𝔼[z₁ z₂]`: a pool of `n` genotyped individuals with genotype matrix
`X`, two GWAS samples `S₁`, `S₂` of the pool (possibly overlapping), effects `β₁`, `β₂` with
`∫ β₁ k β₂ l = (ρ_g / M) [k = l]` (genetic covariance `ρ_g`), noises `ε₁`, `ε₂` with
`∫ ε₁ i ε₂ i' = ρ_e [i = i']` (residual cross-moment `ρ_e` within an individual), effects of
each trait orthogonal to the noise of the other. The structure intentionally does not impose
within-trait moments or phenotype normalization, so it does not identify `ρ_e` with phenotypic
correlation or establish that the scaled scores below are standardized z-scores. -/
structure CrossTraitModel (μ : Measure Ω) (n M : ℕ) where
  /-- The sample of trait 1. -/
  S1 : Finset (Fin n)
  /-- The sample of trait 2. -/
  S2 : Finset (Fin n)
  /-- The genetic covariance `ρ_g`. -/
  rhoG : ℝ
  /-- The environmental covariance `ρ_e`. -/
  rhoE : ℝ
  /-- Effects on trait 1. -/
  beta1 : Fin M → Ω → ℝ
  /-- Effects on trait 2. -/
  beta2 : Fin M → Ω → ℝ
  /-- Noise of trait 1. -/
  eps1 : Fin n → Ω → ℝ
  /-- Noise of trait 2. -/
  eps2 : Fin n → Ω → ℝ
  /-- Square integrability. -/
  memLp_beta1 : ∀ k, MemLp (beta1 k) 2 μ
  /-- Square integrability. -/
  memLp_beta2 : ∀ k, MemLp (beta2 k) 2 μ
  /-- Square integrability. -/
  memLp_eps1 : ∀ i, MemLp (eps1 i) 2 μ
  /-- Square integrability. -/
  memLp_eps2 : ∀ i, MemLp (eps2 i) 2 μ
  /-- `∫ β₁ β₂ᵀ = (ρ_g / M) I`. -/
  integral_beta1_mul_beta2 : ∀ k l, ∫ ω, beta1 k ω * beta2 l ω ∂μ =
    if k = l then rhoG / M else 0
  /-- `∫ ε₁ ε₂ᵀ = ρ_e I`. -/
  integral_eps1_mul_eps2 : ∀ i i', ∫ ω, eps1 i ω * eps2 i' ω ∂μ = if i = i' then rhoE else 0
  /-- `∫ β₁ ε₂ᵀ = 0`. -/
  integral_beta1_mul_eps2 : ∀ k i, ∫ ω, beta1 k ω * eps2 i ω ∂μ = 0
  /-- `∫ ε₁ β₂ᵀ = 0`. -/
  integral_eps1_mul_beta2 : ∀ i k, ∫ ω, eps1 i ω * beta2 k ω ∂μ = 0

namespace CrossTraitModel

variable {μ : Measure Ω} (D : CrossTraitModel μ n M) (X : Matrix (Fin n) (Fin M) ℝ)

/-- The scaled marginal score `z₁ j = √N₁ X_jᵀ y₁ / N₁` of marker `j` for trait 1, computed on
`S₁` with `y₁ = X β₁ + ε₁`. The model does not assert the normalization needed for a z-score. -/
noncomputable def z1 (j : Fin M) (ω : Ω) : ℝ :=
  √(D.S1.card : ℝ) * ((∑ i ∈ D.S1, X i j * (∑ k, X i k * D.beta1 k ω + D.eps1 i ω)) / D.S1.card)

/-- The analogous scaled marginal score `z₂ j` of marker `j` for trait 2, computed on `S₂`. -/
noncomputable def z2 (j : Fin M) (ω : Ω) : ℝ :=
  √(D.S2.card : ℝ) * ((∑ i ∈ D.S2, X i j * (∑ k, X i k * D.beta2 k ω + D.eps2 i ω)) / D.S2.card)

private theorem sampleScore_eq (S : Finset (Fin n)) (β : Fin M → Ω → ℝ) (ε : Fin n → Ω → ℝ)
    (j : Fin M) (ω : Ω) :
    (∑ i ∈ S, X i j * (∑ k, X i k * β k ω + ε i ω)) / S.card =
      ∑ k, sampleCorr X S j k * β k ω + ∑ i, (if i ∈ S then X i j / S.card else 0) * ε i ω := by
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  unfold sampleCorr
  simp_rw [mul_add, Finset.sum_add_distrib, add_div, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, div_mul_eq_mul_div, Finset.sum_div]

/-- **Cross-trait LD-score regression, exact form**: with `N₁ = |S₁|`, `N₂ = |S₂|`,
`𝔼[z₁ j z₂ j] = √(N₁ N₂) (ρ_g / M) ∑_k r¹ j k r² j k + ρ_e (∑_{i ∈ S₁ ∩ S₂} X i j ²) / √(N₁ N₂)`,
with the in-sample correlations `r¹`, `r²` (`sampleCorr`). -/
theorem integral_z_mul_z (j : Fin M) :
    ∫ ω, D.z1 X j ω * D.z2 X j ω ∂μ =
      √((D.S1.card : ℝ) * D.S2.card) * (D.rhoG / M) *
          ∑ k, sampleCorr X D.S1 j k * sampleCorr X D.S2 j k +
        D.rhoE * (∑ i ∈ D.S1 ∩ D.S2, X i j ^ 2) / √((D.S1.card : ℝ) * D.S2.card) := by
  classical
  let f : Fin M ⊕ Fin n → Ω → ℝ := Sum.elim D.beta1 D.eps1
  let g : Fin M ⊕ Fin n → Ω → ℝ := Sum.elim D.beta2 D.eps2
  let a : Fin M ⊕ Fin n → ℝ := Sum.elim (sampleCorr X D.S1 j)
    (fun i => if i ∈ D.S1 then X i j / D.S1.card else 0)
  let b : Fin M ⊕ Fin n → ℝ := Sum.elim (sampleCorr X D.S2 j)
    (fun i => if i ∈ D.S2 then X i j / D.S2.card else 0)
  have hf (u : Fin M ⊕ Fin n) : MemLp (f u) 2 μ := by
    cases u with
    | inl k => exact D.memLp_beta1 k
    | inr i => exact D.memLp_eps1 i
  have hg (u : Fin M ⊕ Fin n) : MemLp (g u) 2 μ := by
    cases u with
    | inl k => exact D.memLp_beta2 k
    | inr i => exact D.memLp_eps2 i
  have h1 (ω : Ω) : D.z1 X j ω = √(D.S1.card : ℝ) * ∑ u, a u * f u ω := by
    rw [z1, sampleScore_eq, Fintype.sum_sum_type]
    rfl
  have h2 (ω : Ω) : D.z2 X j ω = √(D.S2.card : ℝ) * ∑ u, b u * g u ω := by
    rw [z2, sampleScore_eq, Fintype.sum_sum_type]
    rfl
  have hprod (ω : Ω) : D.z1 X j ω * D.z2 X j ω =
      (√(D.S1.card : ℝ) * √(D.S2.card : ℝ)) * ((∑ u, a u * f u ω) * ∑ u, b u * g u ω) := by
    rw [h1, h2]
    ring
  have hov : ∑ i, (if i ∈ D.S1 then X i j / D.S1.card else 0) *
      ((if i ∈ D.S2 then X i j / D.S2.card else 0) * D.rhoE) =
      D.rhoE * (∑ i ∈ D.S1 ∩ D.S2, X i j ^ 2) / (D.S1.card * D.S2.card) := by
    have : ∀ i, (if i ∈ D.S1 then X i j / D.S1.card else 0) *
        ((if i ∈ D.S2 then X i j / D.S2.card else 0) * D.rhoE) =
        if i ∈ D.S1 ∩ D.S2 then X i j ^ 2 * (D.rhoE / (D.S1.card * D.S2.card)) else 0 := by
      intro i
      by_cases h1 : i ∈ D.S1 <;> by_cases h2 : i ∈ D.S2 <;> simp [h1, h2]
      ring
    simp_rw [this]
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_mul]
    ring
  simp_rw [hprod]
  rw [integral_const_mul, integral_sum_mul_sum f g a b hf hg]
  simp only [Fintype.sum_sum_type, f, g, a, b, Sum.elim_inl, Sum.elim_inr,
    D.integral_beta1_mul_beta2, D.integral_eps1_mul_eps2, D.integral_beta1_mul_eps2,
    D.integral_eps1_mul_beta2, mul_zero, Finset.sum_const_zero, add_zero, zero_add, mul_ite,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_assoc]
  have hsum : ∑ k, sampleCorr X D.S1 j k * (sampleCorr X D.S2 j k * (D.rhoG / M)) =
      D.rhoG / M * ∑ k, sampleCorr X D.S1 j k * sampleCorr X D.S2 j k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hov, hsum, Real.sqrt_mul (Nat.cast_nonneg _)]
  generalize ∑ k, sampleCorr X D.S1 j k * sampleCorr X D.S2 j k = A
  have hN₁ : 0 ≤ (D.S1.card : ℝ) := Nat.cast_nonneg _
  have hN₂ : 0 ≤ (D.S2.card : ℝ) := Nat.cast_nonneg _
  generalize (D.S1.card : ℝ) = N₁ at *
  generalize (D.S2.card : ℝ) = N₂ at *
  rcases eq_or_ne N₁ 0 with h | h
  · simp [h]
  rcases eq_or_ne N₂ 0 with h' | h'
  · simp [h']
  have e : N₁ * N₂ = (√N₁ * √N₂) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hN₁, Real.sq_sqrt hN₂]
  have hs₁ : √N₁ ≠ 0 := (Real.sqrt_pos.2 (lt_of_le_of_ne hN₁ (Ne.symm h))).ne'
  have hs₂ : √N₂ ≠ 0 := (Real.sqrt_pos.2 (lt_of_le_of_ne hN₂ (Ne.symm h'))).ne'
  rw [e]
  field_simp

/-- **Equal-LD specialization of the residual cross-moment identity**: if the two samples have
the same LD with marker `j` and the overlap marker is standardized at `j`
(`∑_{i ∈ S₁ ∩ S₂} X i j ² = N_s`), then
`𝔼[z₁ j z₂ j] = √(N₁ N₂) ρ_g ℓ_j / M + ρ_e N_s / √(N₁ N₂)`. Here `ρ_e` is only the residual
cross-moment specified by `CrossTraitModel`; this theorem does not state the Bulik-Sullivan
phenotypic-correlation overlap formula or establish z-score normalization. -/
theorem integral_z_mul_z_of_sameLD (j : Fin M)
    (hLD : ∀ k, sampleCorr X D.S1 j k = sampleCorr X D.S2 j k)
    (hs : ∑ i ∈ D.S1 ∩ D.S2, X i j ^ 2 = (D.S1 ∩ D.S2).card) :
    ∫ ω, D.z1 X j ω * D.z2 X j ω ∂μ =
      √((D.S1.card : ℝ) * D.S2.card) * D.rhoG * (∑ k, sampleCorr X D.S1 j k ^ 2) / M +
        D.rhoE * (D.S1 ∩ D.S2).card / √((D.S1.card : ℝ) * D.S2.card) := by
  rw [D.integral_z_mul_z X j, hs]
  simp_rw [← hLD, ← sq]
  ring

end CrossTraitModel

end CrossTrait

/-! ### The Cochran–Armitage trend test -/

namespace ArmitageTrend

/-! A case–control genotype table: `r i` cases and `s i` controls carry `i ∈ {0, 1, 2}` copies of
the counted allele (real-valued counts). The genotype score is the allele count `i`. -/

variable (r s : Fin 3 → ℝ)

/-- The number of individuals `N = ∑ (r i + s i)`. -/
def total : ℝ := ∑ i, (r i + s i)

/-- The trend numerator `U = ∑ i, i (r i S - s i R)` with `R = ∑ r`, `S = ∑ s`. -/
def numer : ℝ := ∑ i : Fin 3, ((i : ℕ) : ℝ) * (r i * ∑ j, s j - s i * ∑ j, r j)

/-- The pooled genotype-score variance `∑ i² n_i / N - (∑ i n_i / N)²`, `n_i = r i + s i`. -/
noncomputable def scoreVar : ℝ :=
  (∑ i : Fin 3, ((i : ℕ) : ℝ) ^ 2 * (r i + s i)) / total r s -
    ((∑ i : Fin 3, ((i : ℕ) : ℝ) * (r i + s i)) / total r s) ^ 2

/-- The **Cochran–Armitage trend statistic** with scores `0, 1, 2` (Armitage 1955):
`N U² / (R S (N ∑ i² n_i - (∑ i n_i)²))`. -/
noncomputable def trendStat : ℝ :=
  total r s * numer r s ^ 2 / ((∑ i, r i) * (∑ i, s i) *
    (total r s * ∑ i : Fin 3, ((i : ℕ) : ℝ) ^ 2 * (r i + s i) -
      (∑ i : Fin 3, ((i : ℕ) : ℝ) * (r i + s i)) ^ 2))

/-- The squared sample correlation of case status (`1` for cases, `0` for controls) and the
genotype score over the `N` individuals of the table. -/
noncomputable def corrSq : ℝ :=
  ((∑ i : Fin 3, ((i : ℕ) : ℝ) * r i) / total r s -
      (∑ i, r i) / total r s * ((∑ i : Fin 3, ((i : ℕ) : ℝ) * (r i + s i)) / total r s)) ^ 2 /
    (((∑ i, r i) / total r s - ((∑ i, r i) / total r s) ^ 2) * scoreVar r s)

/-- The pooled frequency `p = ∑ i n_i / (2 N)` of the counted allele. -/
noncomputable def alleleFreq : ℝ :=
  (∑ i : Fin 3, ((i : ℕ) : ℝ) * (r i + s i)) / (2 * total r s)

/-- Pearson's statistic `n (a d - b c)² / ((a + b)(c + d)(a + c)(b + d))` of a `2 × 2` table
`[[a, b], [c, d]]` with `n = a + b + c + d`. -/
noncomputable def pearson2x2 (a b c d : ℝ) : ℝ :=
  (a + b + c + d) * (a * d - b * c) ^ 2 / ((a + b) * (c + d) * (a + c) * (b + d))

/-- The **allelic test**: Pearson's statistic of the `2 × 2` table of case and control allele
counts (`2N` alleles). -/
noncomputable def allelicStat : ℝ :=
  pearson2x2 (∑ i : Fin 3, ((i : ℕ) : ℝ) * r i) (2 * ∑ i, r i - ∑ i : Fin 3, ((i : ℕ) : ℝ) * r i)
    (∑ i : Fin 3, ((i : ℕ) : ℝ) * s i) (2 * ∑ i, s i - ∑ i : Fin 3, ((i : ℕ) : ℝ) * s i)

private theorem total_eq : total r s = ∑ i, r i + ∑ i, s i := by
  simp [total, Finset.sum_add_distrib]

private theorem numer_eq : numer r s = (∑ i : Fin 3, ((i : ℕ) : ℝ) * r i) * ∑ i, s i -
    (∑ i : Fin 3, ((i : ℕ) : ℝ) * s i) * ∑ i, r i := by
  simp only [numer, Fin.sum_univ_three]
  ring

private theorem sum_score_eq : ∑ i : Fin 3, ((i : ℕ) : ℝ) * (r i + s i) =
    ∑ i : Fin 3, ((i : ℕ) : ℝ) * r i + ∑ i : Fin 3, ((i : ℕ) : ℝ) * s i := by
  simp only [mul_add, Finset.sum_add_distrib]

/-- **The trend test is `N r²`** (Armitage 1955): the Cochran–Armitage statistic is `N` times
the squared sample correlation of case status and genotype score. (In degenerate tables, where a
denominator vanishes, both sides are `0` by the convention `x / 0 = 0`.) -/
theorem trendStat_eq_total_mul_corrSq : trendStat r s = total r s * corrSq r s := by
  rcases eq_or_ne (total r s) 0 with hT | hT
  · simp [trendStat, hT]
  have hT' := hT
  rw [total_eq] at hT'
  simp only [trendStat, corrSq, scoreVar, numer_eq, sum_score_eq]
  rw [total_eq]
  generalize ∑ i, r i = R at *
  generalize ∑ i, s i = S at *
  generalize ∑ i : Fin 3, ((i : ℕ) : ℝ) * r i = A
  generalize ∑ i : Fin 3, ((i : ℕ) : ℝ) * s i = C
  generalize ∑ i : Fin 3, ((i : ℕ) : ℝ) ^ 2 * (r i + s i) = Q
  have e1 : (A / (R + S) - R / (R + S) * ((A + C) / (R + S))) ^ 2 =
      (A * S - C * R) ^ 2 / (R + S) ^ 4 := by
    field_simp
    ring
  have e2 : (R / (R + S) - (R / (R + S)) ^ 2) * (Q / (R + S) - ((A + C) / (R + S)) ^ 2) =
      R * S * ((R + S) * Q - (A + C) ^ 2) / (R + S) ^ 4 := by
    field_simp
    ring
  rw [e1, e2, div_div_div_cancel_right₀ (pow_ne_zero 4 hT'), mul_div_assoc]

/-- The observed score variance minus the Hardy–Weinberg score variance `2 p q`:
`Var - 2 p (1 - p) = (4 n₀ n₂ - n₁²) / (2 N²)`. -/
theorem scoreVar_sub_hweVar (hN : total r s ≠ 0) :
    scoreVar r s - 2 * alleleFreq r s * (1 - alleleFreq r s) =
      (4 * (r 0 + s 0) * (r 2 + s 2) - (r 1 + s 1) ^ 2) / (2 * total r s ^ 2) := by
  simp only [scoreVar, alleleFreq, total, Fin.sum_univ_three] at hN ⊢
  generalize r 0 + s 0 = n₀ at *
  generalize r 1 + s 1 = n₁ at *
  generalize r 2 + s 2 = n₂ at *
  norm_num
  field_simp
  ring

/-- **Allelic versus trend test** (Sasieni 1997): with cases and controls present, a pooled
allele frequency strictly between `0` and `1` and a positive score variance,
`allelic · 2 p q = trend · Var`. -/
theorem allelicStat_mul_hweVar (hR : 0 < ∑ i, r i) (hS : 0 < ∑ i, s i)
    (hp0 : 0 < alleleFreq r s) (hp1 : alleleFreq r s < 1) (hV : 0 < scoreVar r s) :
    allelicStat r s * (2 * alleleFreq r s * (1 - alleleFreq r s)) =
      trendStat r s * scoreVar r s := by
  have hT : 0 < total r s := by rw [total_eq]; positivity
  have hTRS := total_eq r s
  simp only [allelicStat, trendStat, scoreVar, alleleFreq, numer_eq, sum_score_eq] at hp0 hp1 hV ⊢
  generalize total r s = T at *
  generalize ∑ i, r i = R at *
  generalize ∑ i, s i = S at *
  generalize ∑ i : Fin 3, ((i : ℕ) : ℝ) * r i = A at *
  generalize ∑ i : Fin 3, ((i : ℕ) : ℝ) * s i = C at *
  generalize ∑ i : Fin 3, ((i : ℕ) : ℝ) ^ 2 * (r i + s i) = Q at *
  have hB : 0 < A + C := by
    have := div_pos_iff.1 hp0
    rcases this with h | h
    · exact h.1
    · linarith [h.2]
  have hB2 : A + C < 2 * T := by rwa [div_lt_one (by positivity)] at hp1
  have hV' : 0 < T * Q - (A + C) ^ 2 := by
    have : Q / T - ((A + C) / T) ^ 2 = (T * Q - (A + C) ^ 2) / T ^ 2 := by
      field_simp
    rw [this] at hV
    exact (div_pos_iff_of_pos_right (by positivity)).1 hV
  have hD : 2 * T - (A + C) ≠ 0 := by linarith
  simp only [pearson2x2]
  rw [show A + (2 * R - A) + C + (2 * S - C) = 2 * (R + S) by ring,
    show A * (2 * S - C) - (2 * R - A) * C = 2 * (A * S - C * R) by ring,
    show A + (2 * R - A) = 2 * R by ring, show C + (2 * S - C) = 2 * S by ring,
    show 2 * R - A + (2 * S - C) = 2 * (R + S) - (A + C) by ring]
  subst hTRS
  have hRS : R + S ≠ 0 := hT.ne'
  field_simp

/-- **The allelic test equals the trend test iff the pooled sample is in Hardy–Weinberg
proportions** (`n₁² = 4 n₀ n₂`; Sasieni 1997), whenever the trend numerator is nonzero. -/
theorem allelicStat_eq_trendStat_iff (hR : 0 < ∑ i, r i) (hS : 0 < ∑ i, s i)
    (hp0 : 0 < alleleFreq r s) (hp1 : alleleFreq r s < 1) (hV : 0 < scoreVar r s)
    (hU : numer r s ≠ 0) :
    allelicStat r s = trendStat r s ↔
      (r 1 + s 1) ^ 2 = 4 * (r 0 + s 0) * (r 2 + s 2) := by
  have hT : 0 < total r s := by rw [total_eq]; positivity
  have hp : 0 < 2 * alleleFreq r s * (1 - alleleFreq r s) := by
    have : 0 < 1 - alleleFreq r s := by linarith
    positivity
  have hden : 0 < total r s * ∑ i : Fin 3, ((i : ℕ) : ℝ) ^ 2 * (r i + s i) -
      (∑ i : Fin 3, ((i : ℕ) : ℝ) * (r i + s i)) ^ 2 := by
    have : scoreVar r s = (total r s * ∑ i : Fin 3, ((i : ℕ) : ℝ) ^ 2 * (r i + s i) -
        (∑ i : Fin 3, ((i : ℕ) : ℝ) * (r i + s i)) ^ 2) / total r s ^ 2 := by
      unfold scoreVar
      field_simp
    rw [this] at hV
    exact (div_pos_iff_of_pos_right (by positivity)).1 hV
  have htr : trendStat r s ≠ 0 := by
    unfold trendStat
    exact div_ne_zero (mul_ne_zero hT.ne' (pow_ne_zero 2 hU)) (by positivity)
  have key := allelicStat_mul_hweVar r s hR hS hp0 hp1 hV
  have hdiff := scoreVar_sub_hweVar r s hT.ne'
  have h2T : (0 : ℝ) < 2 * total r s ^ 2 := by positivity
  constructor
  · intro h
    rw [h] at key
    have hv := mul_left_cancel₀ htr key
    rw [← hv, sub_self] at hdiff
    have := (div_eq_zero_iff.1 hdiff.symm).resolve_right h2T.ne'
    linarith
  · intro h
    have h0 : 4 * (r 0 + s 0) * (r 2 + s 2) - (r 1 + s 1) ^ 2 = 0 := by linarith
    rw [h0, zero_div, sub_eq_zero] at hdiff
    rw [hdiff] at key
    exact mul_right_cancel₀ hp.ne' key

end ArmitageTrend

end MathlibExt.Biology.StatisticalGenetics.GenomicPrediction
