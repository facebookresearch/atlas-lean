/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScoreRegression
public import MathlibExt.Biology.StatisticalGenetics.GenomicPrediction
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Polygenic risk scores under linkage disequilibrium: accuracy and calibration

A polygenic risk score (PRS) predicts a phenotype from genotypes `x` of `M` markers by
`ĝ = xᵀ β̂`, where `β̂` are effect estimates from a training GWAS. The quantity it targets is the
genetic value `g = xᵀ β`. This file proves the accuracy and the calibration slope of the score
when the markers are in linkage disequilibrium (LD), extending the uncorrelated-marker formulas of
`MathlibExt.Biology.StatisticalGenetics.GenomicPrediction` (Daetwyler et al. 2008; Dudbridge
2013).

## The model

* **Training.** The LD-score model `LDScore.Model` of Bulik-Sullivan et al. (2015): `N`
  individuals, genotype matrix `X`, phenotype `y = X β + ε`, raw second moments
  `𝔼[β βᵀ] = (h² / M) I`, `𝔼[ε εᵀ] = (1 - h²) I`, `𝔼[β εᵀ] = 0`. The effects are estimated by
  the marginal scores `β̂ = Xᵀ y / N` (`LDScore.Model.betaHat`). With the in-sample LD matrix
  `R j k = X_jᵀ X_k / N` (`ldMatrix`, built from `LDScore.ldCorr`) these are
  `β̂ = R β + e` with `e = Xᵀ ε / N` (`betaHat_eq`), so that
  `𝔼[β β̂ᵀ] = (h² / M) R` (`integral_beta_mul_betaHat`) and
  `𝔼[β̂ β̂ᵀ] = (h² / M) R² + ((1 - h²) / N) R` (`integral_betaHat_mul_betaHat`, `scoreCov`).
  Sampling noise in `β̂` therefore carries the training LD.
* **Target.** Target genotypes `x` with raw second moments `𝔼[x xᵀ] = S` (the target LD matrix)
  and a target phenotype `y = xᵀ β + ε_t` with `ε_t` orthogonal to `x`. Then
  `Cov(y, xᵀ b) = βᵀ S b` and `Var(xᵀ b) = bᵀ S b` (`integral_pheno_mul_score`): the phenotype
  and the genetic value have the same covariance with any score.
* **Accuracy and calibration as ratios of expectations** (the convention of
  `GenomicPrediction.PRSModel.accuracySq`): with `C(a, b) = 𝔼_train[aᵀ S b]` (`quadCov`),
  `accuracySq = C(β, β̂)² / (C(β, β) C(β̂, β̂))` is the squared correlation of `g` and `ĝ`, and
  `calibSlope = C(β, β̂) / C(β̂, β̂)` is the slope of the regression of the phenotype (equally of
  `g`) on the score. These are not the expectations of a sample squared correlation or a sample
  regression slope.

## Main results

* `calibSlope_eq_one_of_orthogonal`, `accuracySq_eq_of_orthogonal`: **calibration criterion.**
  If the estimation error `β - β̂` is orthogonal in `L²` to every coordinate of `β̂`, the
  calibration slope is `1` for every target LD matrix, and the accuracy is
  `C(β̂, β̂) / C(β, β)`.
* `accuracySq_marginal`, `calibSlope_marginal`: **accuracy and calibration of the marginal PRS
  under LD.** If the target LD equals the training LD (`S = R`), `X` is standardized and
  `N, M ≠ 0`, then with `L = ∑_j ℓ_j = tr R²` (`ldScoreSum`, the sum of LD scores) and
  `T = tr R³` (`ldCube`),
  `r² = (h² L / M)² / (h² (h² T / M + (1 - h²) L / N))` and
  `slope = (h² L / M) / (h² T / M + (1 - h²) L / N)`.
* `accuracySq_marginal_of_orthogonal`: with no LD (orthogonal standardized training columns,
  `R = I`) this is `N h² / (N h² + M (1 - h²))`, the value of
  `GenomicPrediction.PRSModel.accuracySq_ofLDScore`.
* `accuracySq_marginal_eq_olsH2Hat`: **the accuracy is identified by LD-score regression.**
  Replacing `h²` in the formula by the unweighted LD-score regression estimator
  `LDScoreRegression.olsH2Hat` applied to the expected association statistics gives the same
  accuracy (it uses the LDSC identity through `olsH2Hat_integral_chiSqStrat`), when the LD
  scores are not all equal.
* `calibSlope_blup`, `accuracySq_blup`: **a calibrated score.** The linear shrinkage
  `β̃ = K β̂` with `K = (h² / M) R (𝔼[β̂ β̂ᵀ])⁻¹` (`shrinkMatrix`, `blupScore`, the best linear
  predictor of `β` from `β̂`) has calibration slope exactly `1` for every target LD matrix,
  provided `𝔼[β̂ β̂ᵀ]` is invertible.

## What is not claimed

With perfect LD (two identical columns) `R` and hence `𝔼[β̂ β̂ᵀ]` are singular: `shrinkMatrix`
is then `0` (Mathlib's inverse of a singular matrix), `blupScore` is `0`, and its "calibration
slope" is the junk value `0 / 0 = 0`; `calibSlope_blup` does not apply. The LD scores of such a
design are all equal, so the LD-score regression slope is not identified and
`accuracySq_marginal_eq_olsH2Hat` does not apply either. The marginal formula itself stays
defined there; it describes the marginal score, not a joint-effect estimate. Sample-level
statements (the distribution of the sample `R²` of a PRS, finite-sample bias of the plug-in
accuracy) are not treated, and the shrinkage of `blupScore` uses the true `h²`. The training
individuals are unrelated (`𝔼[ε εᵀ] = (1 - h²) I`, as in `LDScore.Model`), so relatedness is
not modeled and `KinshipIBD` is not used.

## References

* H. D. Daetwyler, B. Villanueva, J. A. Woolliams, *Accuracy of predicting the genetic risk of
  disease using a genome-wide approach*, PLoS ONE 3 (2008), e3395.
* F. Dudbridge, *Power and predictive accuracy of polygenic risk scores*, PLoS Genet. 9 (2013),
  e1003348.
* B. J. Vilhjálmsson et al., *Modeling linkage disequilibrium increases accuracy of polygenic
  risk scores*, Am. J. Hum. Genet. 97 (2015), 576–592.
* B. K. Bulik-Sullivan et al., *LD Score regression distinguishes confounding from polygenicity
  in genome-wide association studies*, Nat. Genet. 47 (2015), 291–295.
-/

@[expose] public section

open MeasureTheory Matrix
open MathlibExt.Biology.StatisticalGenetics.LDScore
  MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
  MathlibExt.Biology.StatisticalGenetics.LDScoreRegression
  MathlibExt.Probability.FiniteProbability
open MathlibExt.Biology.StatisticalGenetics.GenomicPrediction (HasOrthogonalColumns PRSModel)

namespace MathlibExt.Biology.StatisticalGenetics.PolygenicRiskScore

/-! ### Second-moment bookkeeping -/

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

/-- For an orthogonal family `f` with `∫ f k f l = b k [k = l]`, the cross moment of two linear
combinations is `∑ k, a k c k b k`. -/
private theorem integral_lin_mul_lin {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Ω → ℝ)
    (a c b : ι → ℝ) (hf : ∀ k, MemLp (f k) 2 μ)
    (hm : ∀ k l, ∫ ω, f k ω * f l ω ∂μ = if k = l then b k else 0) :
    ∫ ω, (∑ k, a k * f k ω) * (∑ l, c l * f l ω) ∂μ = ∑ k, a k * c k * b k := by
  rw [integral_sum_mul_sum f f a c hf hf]
  simp_rw [hm, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end Moments

/-! ### Target population, accuracy and calibration -/

section Target

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {M : ℕ}

/-- **Target-population covariances.** If the target genotypes have raw second moments
`∫ x j x k = S j k` and the target phenotype is `y = xᵀ a + e` with `e` orthogonal to every
`x k`, then `∫ y · (xᵀ b) = aᵀ S b`. With `e = 0` this is the covariance of the scores `xᵀ a` and
`xᵀ b` (for a probability measure and mean-zero genotypes): the phenotype and the genetic value
`xᵀ a` have the same covariance with every score. -/
theorem integral_pheno_mul_score {Ξ : Type*} {mΞ : MeasurableSpace Ξ} {ν : Measure Ξ}
    (x : Fin M → Ξ → ℝ) (e : Ξ → ℝ) (hx : ∀ j, MemLp (x j) 2 ν) (he : MemLp e 2 ν)
    (S : Matrix (Fin M) (Fin M) ℝ) (hxx : ∀ j k, ∫ ξ, x j ξ * x k ξ ∂ν = S j k)
    (hex : ∀ k, ∫ ξ, e ξ * x k ξ ∂ν = 0) (a b : Fin M → ℝ) :
    ∫ ξ, (∑ j, a j * x j ξ + e ξ) * (∑ k, b k * x k ξ) ∂ν = ∑ j, ∑ k, a j * S j k * b k := by
  have h1 : Integrable (fun ξ => (∑ j, a j * x j ξ) * (∑ k, b k * x k ξ)) ν := by
    have hA := memLp_finsetSum Finset.univ fun j _ => (hx j).const_mul (a j)
    have hB := memLp_finsetSum Finset.univ fun k _ => (hx k).const_mul (b k)
    exact hA.integrable_mul hB
  have h2i (k : Fin M) : Integrable (fun ξ => b k * (e ξ * x k ξ)) ν :=
    (he.integrable_mul (hx k)).const_mul _
  have hsplit (ξ : Ξ) : (∑ j, a j * x j ξ + e ξ) * (∑ k, b k * x k ξ) =
      (∑ j, a j * x j ξ) * (∑ k, b k * x k ξ) + ∑ k, b k * (e ξ * x k ξ) := by
    rw [add_mul]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hsplit]
  rw [integral_add h1 (integrable_finsetSum _ fun k _ => h2i k),
    integral_sum_mul_sum x x a b hx hx, integral_finsetSum _ fun k _ => h2i k]
  simp only [integral_const_mul, hxx, hex, mul_zero, Finset.sum_const_zero, add_zero]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- The training expectation `C(a, b) = 𝔼[aᵀ S b] = ∫ ∑ j k, a j S j k b k` of the target-population
covariance of the scores `xᵀ a` and `xᵀ b` (`integral_pheno_mul_score`), for random effect
vectors `a`, `b` and target LD matrix `S`. -/
noncomputable def quadCov (μ : Measure Ω) (S : Matrix (Fin M) (Fin M) ℝ)
    (a b : Fin M → Ω → ℝ) : ℝ :=
  ∫ ω, ∑ j, ∑ k, a j ω * S j k * b k ω ∂μ

/-- `C(a, b) = ∑ j k, S j k 𝔼[a j b k]`. -/
theorem quadCov_eq (S : Matrix (Fin M) (Fin M) ℝ) (a b : Fin M → Ω → ℝ)
    (ha : ∀ j, MemLp (a j) 2 μ) (hb : ∀ k, MemLp (b k) 2 μ) :
    quadCov μ S a b = ∑ j, ∑ k, S j k * ∫ ω, a j ω * b k ω ∂μ := by
  have hp (j k : Fin M) : Integrable (fun ω => S j k * (a j ω * b k ω)) μ :=
    ((ha j).integrable_mul (hb k)).const_mul _
  have he : (fun ω => ∑ j, ∑ k, a j ω * S j k * b k ω) =
      fun ω => ∑ j, ∑ k, S j k * (a j ω * b k ω) := by
    funext ω
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [quadCov, he, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hp j k]
  simp_rw [integral_finsetSum _ fun k _ => hp _ k, integral_const_mul]

/-- The **squared accuracy** of the score `xᵀ β̂` for the genetic value `xᵀ β` in a target
population with LD matrix `S`, as a ratio of expectations over training:
`C(β, β̂)² / (C(β, β) C(β̂, β̂))`. -/
noncomputable def accuracySq (μ : Measure Ω) (S : Matrix (Fin M) (Fin M) ℝ)
    (β βh : Fin M → Ω → ℝ) : ℝ :=
  quadCov μ S β βh ^ 2 / (quadCov μ S β β * quadCov μ S βh βh)

/-- The **calibration slope** of the score `xᵀ β̂`: the slope `C(β, β̂) / C(β̂, β̂)` of the
regression of the target phenotype (equally, of the genetic value) on the score, as a ratio of
expectations over training. A score is calibrated when it is `1`. -/
noncomputable def calibSlope (μ : Measure Ω) (S : Matrix (Fin M) (Fin M) ℝ)
    (β βh : Fin M → Ω → ℝ) : ℝ :=
  quadCov μ S β βh / quadCov μ S βh βh

/-- If the estimation error `β - β̂` is orthogonal to every coordinate of `β̂`, then
`C(β, β̂) = C(β̂, β̂)` for every target LD matrix. -/
theorem quadCov_eq_of_orthogonal (S : Matrix (Fin M) (Fin M) ℝ) (β βh : Fin M → Ω → ℝ)
    (hβ : ∀ k, MemLp (β k) 2 μ) (hβh : ∀ k, MemLp (βh k) 2 μ)
    (horth : ∀ k l, ∫ ω, (β k ω - βh k ω) * βh l ω ∂μ = 0) :
    quadCov μ S β βh = quadCov μ S βh βh := by
  rw [quadCov_eq S β βh hβ hβh, quadCov_eq S βh βh hβh hβh]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have hs := integral_sub (μ := μ) (f := fun ω => β j ω * βh k ω)
    (g := fun ω => βh j ω * βh k ω) ((hβ j).integrable_mul (hβh k))
    ((hβh j).integrable_mul (hβh k))
  have h := horth j k
  rw [show (fun ω => (β j ω - βh j ω) * βh k ω) =
      fun ω => β j ω * βh k ω - βh j ω * βh k ω from funext fun ω => by ring] at h
  rw [show ∫ ω, β j ω * βh k ω ∂μ = ∫ ω, βh j ω * βh k ω ∂μ by linarith]

/-- **Calibration criterion.** If the estimation error `β - β̂` is orthogonal in `L²` to every
coordinate of `β̂` (as for the best linear predictor of `β` from the data), the calibration slope
is `1` for every target LD matrix `S` with `C(β̂, β̂) ≠ 0`. -/
theorem calibSlope_eq_one_of_orthogonal (S : Matrix (Fin M) (Fin M) ℝ) (β βh : Fin M → Ω → ℝ)
    (hβ : ∀ k, MemLp (β k) 2 μ) (hβh : ∀ k, MemLp (βh k) 2 μ)
    (horth : ∀ k l, ∫ ω, (β k ω - βh k ω) * βh l ω ∂μ = 0)
    (hV : quadCov μ S βh βh ≠ 0) : calibSlope μ S β βh = 1 := by
  rw [calibSlope, quadCov_eq_of_orthogonal S β βh hβ hβh horth, div_self hV]

/-- For a calibrated score (orthogonal estimation error) the squared accuracy is the variance
ratio `C(β̂, β̂) / C(β, β)`. -/
theorem accuracySq_eq_of_orthogonal (S : Matrix (Fin M) (Fin M) ℝ) (β βh : Fin M → Ω → ℝ)
    (hβ : ∀ k, MemLp (β k) 2 μ) (hβh : ∀ k, MemLp (βh k) 2 μ)
    (horth : ∀ k l, ∫ ω, (β k ω - βh k ω) * βh l ω ∂μ = 0)
    (hV : quadCov μ S βh βh ≠ 0) :
    accuracySq μ S β βh = quadCov μ S βh βh / quadCov μ S β β := by
  rw [accuracySq, quadCov_eq_of_orthogonal S β βh hβ hβh horth, sq,
    mul_div_mul_right _ _ hV]

end Target

/-! ### The marginal PRS from the LD-score model -/

section Marginal

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {N M : ℕ}

/-- The in-sample LD matrix `R j k = X_jᵀ X_k / N` (`LDScore.ldCorr`; the sample correlation
matrix for a standardized genotype matrix). -/
noncomputable def ldMatrix (X : Matrix (Fin N) (Fin M) ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  Matrix.of (ldCorr X)

@[simp] theorem ldMatrix_apply (X : Matrix (Fin N) (Fin M) ℝ) (j k : Fin M) :
    ldMatrix X j k = ldCorr X j k := rfl

theorem ldCorr_comm (X : Matrix (Fin N) (Fin M) ℝ) (j k : Fin M) :
    ldCorr X j k = ldCorr X k j := by
  simp only [ldCorr, mul_comm]

/-- The sum of LD scores `L = ∑ j, ℓ j = tr R²`. -/
noncomputable def ldScoreSum (X : Matrix (Fin N) (Fin M) ℝ) : ℝ := ∑ j, ldScore X j

/-- The third LD moment `T = ∑ j l k, R j l R j k R l k = tr R³`. -/
noncomputable def ldCube (X : Matrix (Fin N) (Fin M) ℝ) : ℝ :=
  ∑ j, ∑ l, ∑ k, ldCorr X j l * ldCorr X j k * ldCorr X l k

/-- The accuracy formula `(h² L / M)² / (h² (h² T / M + (1 - h²) L / N))`. -/
noncomputable def accuracyFormula (N M : ℕ) (h2 L T : ℝ) : ℝ :=
  (h2 / M * L) ^ 2 / (h2 * (h2 / M * T + (1 - h2) / N * L))

/-- The calibration-slope formula `(h² L / M) / (h² T / M + (1 - h²) L / N)`. -/
noncomputable def slopeFormula (N M : ℕ) (h2 L T : ℝ) : ℝ :=
  (h2 / M * L) / (h2 / M * T + (1 - h2) / N * L)

/-- The `L²` covariance matrix of the marginal scores,
`𝔼[β̂ β̂ᵀ] = (h² / M) R² + ((1 - h²) / N) R`. -/
noncomputable def scoreCov (N M : ℕ) (h2 : ℝ) (X : Matrix (Fin N) (Fin M) ℝ) :
    Matrix (Fin M) (Fin M) ℝ :=
  (h2 / M) • (ldMatrix X * ldMatrix X) + ((1 - h2) / N) • ldMatrix X

variable (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ)

/-- The marginal scores are the LD-smeared effects plus sampling noise:
`β̂ j = ∑ k, R j k β k + ∑ i, (X i j / N) ε i`. -/
theorem betaHat_eq (j : Fin M) (ω : Ω) :
    D.betaHat X j ω = ∑ k, ldCorr X j k * D.beta k ω + ∑ i, (X i j / N) * D.eps i ω := by
  unfold Model.betaHat Model.pheno ldCorr
  simp_rw [mul_add, Finset.sum_add_distrib, add_div, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, div_mul_eq_mul_div, Finset.sum_div]

/-- Effects and noise as one orthogonal family indexed by `Fin M ⊕ Fin N`. -/
private def fam : Fin M ⊕ Fin N → Ω → ℝ := Sum.elim D.beta D.eps

/-- The second moments of `fam`. -/
private noncomputable def famVar : Fin M ⊕ Fin N → ℝ :=
  Sum.elim (fun _ => D.h2 / M) (fun _ => 1 - D.h2)

/-- The coefficients of `β̂ j` on `fam`. -/
private noncomputable def coef (j : Fin M) : Fin M ⊕ Fin N → ℝ :=
  Sum.elim (ldCorr X j) (fun i => X i j / N)

private theorem memLp_fam (s : Fin M ⊕ Fin N) : MemLp (fam D s) 2 μ := by
  cases s with
  | inl k => exact D.memLp_beta k
  | inr i => exact D.memLp_eps i

private theorem integral_fam_mul (s t : Fin M ⊕ Fin N) :
    ∫ ω, fam D s ω * fam D t ω ∂μ = if s = t then famVar D s else 0 := by
  cases s with
  | inl k =>
    cases t with
    | inl l => simpa [fam, famVar] using D.integral_beta_mul k l
    | inr i => simpa [fam] using D.integral_beta_mul_eps k i
  | inr i =>
    cases t with
    | inl k => simpa [fam, mul_comm] using D.integral_beta_mul_eps k i
    | inr i' => simpa [fam, famVar] using D.integral_eps_mul i i'

private theorem betaHat_eq_fam (j : Fin M) (ω : Ω) :
    D.betaHat X j ω = ∑ s, coef X j s * fam D s ω := by
  rw [betaHat_eq, Fintype.sum_sum_type]
  rfl

private theorem beta_eq_fam (k : Fin M) (ω : Ω) :
    D.beta k ω = ∑ s, (if s = Sum.inl k then 1 else 0) * fam D s ω := by
  simp [fam]

/-- The marginal scores are square integrable. -/
theorem memLp_betaHat (j : Fin M) : MemLp (D.betaHat X j) 2 μ := by
  have h := memLp_finsetSum Finset.univ fun s _ => (memLp_fam D s (μ := μ)).const_mul (coef X j s)
  convert h using 1
  funext ω
  exact betaHat_eq_fam D X j ω

/-- `𝔼[β k β̂ l] = (h² / M) R l k`. -/
theorem integral_beta_mul_betaHat (k l : Fin M) :
    ∫ ω, D.beta k ω * D.betaHat X l ω ∂μ = D.h2 / M * ldCorr X l k := by
  classical
  simp_rw [beta_eq_fam D k, betaHat_eq_fam D X l]
  rw [integral_lin_mul_lin (fam D) _ _ (famVar D) (memLp_fam D) (integral_fam_mul D)]
  simp [coef, famVar, mul_comm]

/-- `𝔼[β̂ j β̂ l] = (h² / M) (R²) j l + ((1 - h²) / N) R j l`, the entries of `scoreCov`. -/
theorem integral_betaHat_mul_betaHat (j l : Fin M) :
    ∫ ω, D.betaHat X j ω * D.betaHat X l ω ∂μ = scoreCov N M D.h2 X j l := by
  classical
  simp_rw [betaHat_eq_fam D X j, betaHat_eq_fam D X l]
  rw [integral_lin_mul_lin (fam D) _ _ (famVar D) (memLp_fam D) (integral_fam_mul D)]
  simp only [Fintype.sum_sum_type, coef, famVar, Sum.elim_inl, Sum.elim_inr, scoreCov,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_apply, ldMatrix_apply]
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [ldCorr_comm X k l]; ring
  · simp only [ldCorr]
    rw [Finset.sum_div, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- `C(β, β̂) = (h² / M) L` with target LD `R`. -/
theorem quadCov_beta_betaHat :
    quadCov μ (ldMatrix X) D.beta (D.betaHat X) = D.h2 / M * ldScoreSum X := by
  rw [quadCov_eq _ _ _ D.memLp_beta (memLp_betaHat D X), ldScoreSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [integral_beta_mul_betaHat, ldMatrix_apply, ldScore, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [ldCorr_comm X k j]; ring

/-- `C(β, β) = (h² / M) ∑ j, R j j` with target LD `R`. -/
theorem quadCov_beta_beta :
    quadCov μ (ldMatrix X) D.beta D.beta = D.h2 / M * ∑ j, ldCorr X j j := by
  rw [quadCov_eq _ _ _ D.memLp_beta D.memLp_beta, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [D.integral_beta_mul, mul_comm]

/-- For a standardized genotype matrix and `N, M ≠ 0`, `C(β, β) = h²`. -/
theorem quadCov_beta_beta_of_standardized (hX : IsStandardized X) (hN : N ≠ 0) (hM : M ≠ 0) :
    quadCov μ (ldMatrix X) D.beta D.beta = D.h2 := by
  rw [quadCov_beta_beta]
  simp only [hX.ldCorr_self hN, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  field_simp

/-- `C(β̂, β̂) = (h² / M) T + ((1 - h²) / N) L` with target LD `R`. -/
theorem quadCov_betaHat_betaHat :
    quadCov μ (ldMatrix X) (D.betaHat X) (D.betaHat X) =
      D.h2 / M * ldCube X + (1 - D.h2) / N * ldScoreSum X := by
  rw [quadCov_eq _ _ _ (memLp_betaHat D X) (memLp_betaHat D X), ldCube, ldScoreSum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ldScore, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_betaHat_mul_betaHat]
  simp only [scoreCov, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_apply, ldMatrix_apply]
  have h1 : ∑ k, ldCorr X j k * ldCorr X k l = ∑ k, ldCorr X j k * ldCorr X l k :=
    Finset.sum_congr rfl fun k _ => by rw [ldCorr_comm X k l]
  have h2 : ∑ k, ldCorr X j l * ldCorr X j k * ldCorr X l k =
      ldCorr X j l * ∑ k, ldCorr X j k * ldCorr X l k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h1, h2]
  ring

/-- **Accuracy of the marginal PRS under LD.** If the target LD equals the training LD `R`, the
genotype matrix is standardized and `N, M ≠ 0`, the squared accuracy of `xᵀ β̂` is
`(h² L / M)² / (h² (h² T / M + (1 - h²) L / N))` with `L = tr R²` the sum of LD scores and
`T = tr R³`. -/
theorem accuracySq_marginal (hX : IsStandardized X) (hN : N ≠ 0) (hM : M ≠ 0) :
    accuracySq μ (ldMatrix X) D.beta (D.betaHat X) =
      accuracyFormula N M D.h2 (ldScoreSum X) (ldCube X) := by
  rw [accuracySq, quadCov_beta_betaHat, quadCov_beta_beta_of_standardized D X hX hN hM,
    quadCov_betaHat_betaHat, accuracyFormula]

/-- **Calibration slope of the marginal PRS under LD.** If the target LD equals the training LD
`R`, the slope of the regression of the phenotype on `xᵀ β̂` is
`(h² L / M) / (h² T / M + (1 - h²) L / N)`; it is in general not `1`. -/
theorem calibSlope_marginal :
    calibSlope μ (ldMatrix X) D.beta (D.betaHat X) =
      slopeFormula N M D.h2 (ldScoreSum X) (ldCube X) := by
  rw [calibSlope, quadCov_beta_betaHat, quadCov_betaHat_betaHat, slopeFormula]

/-- With orthogonal training columns of sum of squares `N` (no LD), `R = I`. -/
theorem ldCorr_of_orthogonal (hX : HasOrthogonalColumns X) (hN : N ≠ 0) (j k : Fin M) :
    ldCorr X j k = if j = k then 1 else 0 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [ldCorr, hX j k]
  split_ifs
  · exact div_self hN'
  · exact zero_div _

/-- **No LD.** With orthogonal training columns of sum of squares `N` and `N, M ≠ 0`, the
marginal PRS has squared accuracy `N h² / (N h² + M (1 - h²))`. -/
theorem accuracySq_marginal_of_orthogonal (hX : HasOrthogonalColumns X) (hN : N ≠ 0)
    (hM : M ≠ 0) :
    accuracySq μ (ldMatrix X) D.beta (D.betaHat X) =
      N * D.h2 / (N * D.h2 + M * (1 - D.h2)) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hL : ldScoreSum X = M := by
    simp [ldScoreSum, ldScore, ldCorr_of_orthogonal X hX hN]
  have hT : ldCube X = M := by
    simp [ldCube, ldCorr_of_orthogonal X hX hN]
  have hd : ∑ j, ldCorr X j j = M := by
    simp [ldCorr_of_orthogonal X hX hN]
  rw [accuracySq, quadCov_beta_betaHat, quadCov_beta_beta, quadCov_betaHat_betaHat, hL, hT, hd,
    div_mul_cancel₀ _ hM']
  rcases eq_or_ne D.h2 0 with h | h
  · simp [h]
  rw [sq, mul_div_mul_left _ _ h, ← mul_div_mul_left _ _ hN']
  congr 1
  field_simp

/-- The no-LD accuracy agrees with `GenomicPrediction.PRSModel.accuracySq_ofLDScore`. -/
theorem accuracySq_marginal_eq_ofLDScore (hX : HasOrthogonalColumns X) (hN : N ≠ 0)
    (hM : M ≠ 0) :
    accuracySq μ (ldMatrix X) D.beta (D.betaHat X) = (PRSModel.ofLDScore D X hX).accuracySq := by
  rw [accuracySq_marginal_of_orthogonal D X hX hN hM,
    PRSModel.accuracySq_ofLDScore D X hX hN hM]

/-- The association statistics of the LD-score model are the stratified ones with no
stratification shift. -/
theorem chiSq_eq_chiSqStrat (c : Fin N → ℝ) (j : Fin M) (ω : Ω) :
    D.chiSq X j ω = chiSqStrat D X 0 c j ω := by
  simp [chiSqStrat, betaHatStrat, phenoStrat, Model.chiSq, Model.betaHat]

/-- **LD-score regression identifies `h²` from the expected statistics.** For a probability
measure, mean-zero effects and noise, a standardized genotype matrix whose LD scores are not all
equal, and `N, M ≠ 0`, the unweighted LD-score regression estimator applied to the expected
association statistics `𝔼[χ²_j]` returns `h²` (`LDScoreRegression.olsH2Hat_integral_chiSqStrat`,
from the LDSC identity `𝔼[χ²_j] = 1 + N h² ℓ_j / M - h²`). -/
theorem olsH2Hat_integral_chiSq [IsProbabilityMeasure μ] (hX : IsStandardized X) (hN : N ≠ 0)
    (hM : M ≠ 0) (hℓ : sxy (ldScore X) (ldScore X) ≠ 0) (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0)
    (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) :
    olsH2Hat N M (ldScore X) (fun j => ∫ ω, D.chiSq X j ω ∂μ) = D.h2 := by
  simp_rw [chiSq_eq_chiSqStrat D X 0]
  exact olsH2Hat_integral_chiSqStrat D X hN hM hX hℓ hβ hε 0 0 (a := 0) fun j => by simp

/-- **The PRS accuracy is identified by LD-score regression.** Under the assumptions of
`accuracySq_marginal` and `olsH2Hat_integral_chiSq`, the squared accuracy of the marginal PRS is
the accuracy formula evaluated at the LD-score regression estimate of `h²` computed from the
expected association statistics: it is a function of summary-level quantities (expected `χ²`,
LD scores, `tr R³`, `N`, `M`). -/
theorem accuracySq_marginal_eq_olsH2Hat [IsProbabilityMeasure μ] (hX : IsStandardized X)
    (hN : N ≠ 0) (hM : M ≠ 0) (hℓ : sxy (ldScore X) (ldScore X) ≠ 0)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) :
    accuracySq μ (ldMatrix X) D.beta (D.betaHat X) =
      accuracyFormula N M (olsH2Hat N M (ldScore X) fun j => ∫ ω, D.chiSq X j ω ∂μ)
        (ldScoreSum X) (ldCube X) := by
  rw [olsH2Hat_integral_chiSq D X hX hN hM hℓ hβ hε, accuracySq_marginal D X hX hN hM]

/-- The calibration slope is identified by LD-score regression in the same way. -/
theorem calibSlope_marginal_eq_olsH2Hat [IsProbabilityMeasure μ] (hX : IsStandardized X)
    (hN : N ≠ 0) (hM : M ≠ 0) (hℓ : sxy (ldScore X) (ldScore X) ≠ 0)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) :
    calibSlope μ (ldMatrix X) D.beta (D.betaHat X) =
      slopeFormula N M (olsH2Hat N M (ldScore X) fun j => ∫ ω, D.chiSq X j ω ∂μ)
        (ldScoreSum X) (ldCube X) := by
  rw [olsH2Hat_integral_chiSq D X hX hN hM hℓ hβ hε, calibSlope_marginal D X]

end Marginal

/-! ### A calibrated score: best linear shrinkage of the marginal estimates -/

section BLUP

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {N M : ℕ}

/-- The shrinkage matrix `K = (h² / M) R V⁻¹` with `V = scoreCov` the covariance of the marginal
scores: `K β̂` is the best linear predictor of `β` from `β̂` when `V` is invertible. (When `V` is
singular, Mathlib's inverse is `0` and so is `K`.) -/
noncomputable def shrinkMatrix (N M : ℕ) (h2 : ℝ) (X : Matrix (Fin N) (Fin M) ℝ) :
    Matrix (Fin M) (Fin M) ℝ :=
  ((h2 / M) • ldMatrix X) * (scoreCov N M h2 X)⁻¹

variable (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ)

/-- The shrunk effect estimates `β̃ = K β̂`. -/
noncomputable def blupScore (k : Fin M) (ω : Ω) : ℝ :=
  ∑ n, shrinkMatrix N M D.h2 X k n * D.betaHat X n ω

theorem memLp_blupScore (k : Fin M) : MemLp (blupScore D X k) 2 μ :=
  memLp_finsetSum _ fun n _ => (memLp_betaHat D X n).const_mul _

/-- When `V` is invertible, the shrinkage error `β - K β̂` is orthogonal to every marginal
score. -/
theorem integral_sub_blupScore_mul_betaHat (hV : IsUnit (scoreCov N M D.h2 X).det)
    (k l : Fin M) :
    ∫ ω, (D.beta k ω - blupScore D X k ω) * D.betaHat X l ω ∂μ = 0 := by
  have hi2 (n : Fin M) : Integrable (fun ω =>
      shrinkMatrix N M D.h2 X k n * (D.betaHat X n ω * D.betaHat X l ω)) μ :=
    ((memLp_betaHat D X n).integrable_mul (memLp_betaHat D X l)).const_mul _
  have he : (fun ω => (D.beta k ω - blupScore D X k ω) * D.betaHat X l ω) = fun ω =>
      D.beta k ω * D.betaHat X l ω -
        ∑ n, shrinkMatrix N M D.h2 X k n * (D.betaHat X n ω * D.betaHat X l ω) := by
    funext ω
    rw [blupScore, sub_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [he, integral_sub (f := fun ω => D.beta k ω * D.betaHat X l ω)
    ((D.memLp_beta k).integrable_mul (memLp_betaHat D X l))
    (integrable_finsetSum _ fun n _ => hi2 n), integral_finsetSum _ fun n _ => hi2 n]
  simp_rw [integral_const_mul, integral_betaHat_mul_betaHat, integral_beta_mul_betaHat]
  have hKV : shrinkMatrix N M D.h2 X * scoreCov N M D.h2 X = (D.h2 / M) • ldMatrix X := by
    rw [shrinkMatrix, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hV, Matrix.mul_one]
  have h := congrFun (congrFun hKV k) l
  rw [Matrix.mul_apply, Matrix.smul_apply, ldMatrix_apply, smul_eq_mul] at h
  rw [h, ldCorr_comm X l k, sub_self]

/-- When `V` is invertible, the shrinkage error `β - β̃` is orthogonal to every coordinate of
`β̃`. -/
theorem integral_sub_blupScore_mul_blupScore (hV : IsUnit (scoreCov N M D.h2 X).det)
    (k l : Fin M) :
    ∫ ω, (D.beta k ω - blupScore D X k ω) * blupScore D X l ω ∂μ = 0 := by
  have hi (n : Fin M) : Integrable (fun ω => shrinkMatrix N M D.h2 X l n *
      ((D.beta k ω - blupScore D X k ω) * D.betaHat X n ω)) μ :=
    (((D.memLp_beta k).sub (memLp_blupScore D X k)).integrable_mul
      (memLp_betaHat D X n)).const_mul _
  have he : (fun ω => (D.beta k ω - blupScore D X k ω) * blupScore D X l ω) = fun ω =>
      ∑ n, shrinkMatrix N M D.h2 X l n *
        ((D.beta k ω - blupScore D X k ω) * D.betaHat X n ω) := by
    funext ω
    rw [show blupScore D X l ω = ∑ n, shrinkMatrix N M D.h2 X l n * D.betaHat X n ω from rfl,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [he, integral_finsetSum _ fun n _ => hi n]
  simp_rw [integral_const_mul, integral_sub_blupScore_mul_betaHat D X hV, mul_zero,
    Finset.sum_const_zero]

/-- **The shrunk PRS is calibrated.** If the covariance `V` of the marginal scores is invertible,
the PRS `xᵀ β̃` built from the shrunk estimates `β̃ = (h² / M) R V⁻¹ β̂` has calibration slope
exactly `1` in every target population (any target LD matrix `S` with `C(β̃, β̃) ≠ 0`). -/
theorem calibSlope_blup (S : Matrix (Fin M) (Fin M) ℝ) (hV : IsUnit (scoreCov N M D.h2 X).det)
    (hS : quadCov μ S (blupScore D X) (blupScore D X) ≠ 0) :
    calibSlope μ S D.beta (blupScore D X) = 1 :=
  calibSlope_eq_one_of_orthogonal S _ _ D.memLp_beta (memLp_blupScore D X)
    (integral_sub_blupScore_mul_blupScore D X hV) hS

/-- The squared accuracy of the shrunk PRS is the variance ratio `C(β̃, β̃) / C(β, β)`. -/
theorem accuracySq_blup (S : Matrix (Fin M) (Fin M) ℝ) (hV : IsUnit (scoreCov N M D.h2 X).det)
    (hS : quadCov μ S (blupScore D X) (blupScore D X) ≠ 0) :
    accuracySq μ S D.beta (blupScore D X) =
      quadCov μ S (blupScore D X) (blupScore D X) / quadCov μ S D.beta D.beta :=
  accuracySq_eq_of_orthogonal S _ _ D.memLp_beta (memLp_blupScore D X)
    (integral_sub_blupScore_mul_blupScore D X hV) hS

end BLUP

end MathlibExt.Biology.StatisticalGenetics.PolygenicRiskScore
