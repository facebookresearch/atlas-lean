/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.ProbabilisticPCA
public import MathlibExt.Probability.Distributions.GaussianMLE

/-!
# Probabilistic PCA: the likelihood

Maximum-likelihood facts for probabilistic PCA (Tipping and Bishop, *Probabilistic principal
component analysis*, J. R. Stat. Soc. B 61, 1999; Bishop, *Pattern Recognition and Machine
Learning*, Section 12.2.1), whose observation `x = W z + μ + ε` has law `N(μ, W Wᵀ + σ² I)`
(`ppca_map_eq`, `LatentVariable/ProbabilisticPCA.lean`).

Main results:

* `ppcaCov` (`W Wᵀ + σ² I`), `ppcaCov_posDef`; `ppca_map_eq_withDensity`: **for `σ² > 0` the
  observation has the Gaussian density** `N(x | μ, W Wᵀ + σ² I)`, so `logLik` is its
  log-likelihood.
* `logLik_le_sampleMean`: **the MLE of `μ` is the sample mean**, for every `W` and `σ²`.
* `logLik_le_gaussianMLE`: when the sample covariance is positive definite, the likelihood is at
  most that of the Gaussian with the sample mean and sample covariance (MathlibExt's
  `sum_mul_log_multivariateGaussianPDFReal_le_of_posDef`); `IsMLE`, `isMLE_of_sampleCov_eq`:
  **if the sample covariance has the form `W₀ W₀ᵀ + σ₀² I` with `σ₀² > 0`, then `(x̄, W₀, σ₀²)` is a
  maximum-likelihood estimate**.
* `logLik_zero_le`: with no latent factors (`W = 0`) the MLE of `σ²` is `tr S / d`, for any data
  with a positive total sample variance (rank-deficient data included).

Not covered: Tipping and Bishop's principal-subspace theorem for a general sample covariance
(`W_ML = U_q (Λ_q - σ² I)^{1/2} R`, `σ²_ML` the mean discarded eigenvalue). Its proof combines
von Neumann's trace inequality (MathlibExt's `exists_perm_sum_mul_eigenvalues_le_trace_mul`) with
a constrained optimization over the spectrum of `W Wᵀ + σ² I`; the latter is not done here.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.LatentVariable.ProbabilisticPCA

open MeasureTheory ProbabilityTheory Matrix WithLp Real MetaMathlibExt
open scoped RealInnerProductSpace

variable {q d N : ℕ}

/-- The probabilistic PCA covariance `W Wᵀ + σ² I`. -/
def ppcaCov (W : Matrix (Fin d) (Fin q) ℝ) (σ2 : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  W * Wᵀ + σ2 • 1

theorem ppcaCov_posDef (W : Matrix (Fin d) (Fin q) ℝ) {σ2 : ℝ} (hσ : 0 < σ2) :
    (ppcaCov W σ2).PosDef := by
  have hWW : (W * Wᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose W
  exact PosDef.posSemidef_add hWW (PosDef.one.smul hσ)

/-- **The density of the probabilistic PCA observation**: for `σ² > 0`, the law of
`x = W z + μ + ε` has density `N(x | μ, W Wᵀ + σ² I)` with respect to Lebesgue measure (the
marginal `ppca_map_eq` with MathlibExt's `multivariateGaussian_eq_withDensity`). -/
theorem ppca_map_eq_withDensity {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → EuclideanSpace ℝ (Fin q)} {E : Ω → EuclideanSpace ℝ (Fin d)}
    {σ2 : ℝ} (hσ : 0 < σ2) (hZ : HasLaw Z (stdGaussian _) P)
    (hE : HasLaw E (multivariateGaussian 0 (σ2 • 1)) P) (hind : IndepFun Z E P)
    (W : Matrix (Fin d) (Fin q) ℝ) (μ : EuclideanSpace ℝ (Fin d)) :
    P.map (fun ω => toEuclideanLin W (Z ω) + μ + E ω) =
      volume.withDensity fun x =>
        ENNReal.ofReal (multivariateGaussianPDFReal μ (ppcaCov W σ2) x) := by
  rw [ppca_map_eq hσ.le hZ hE hind W μ]
  exact multivariateGaussian_eq_withDensity μ (ppcaCov_posDef W hσ)

/-- The probabilistic PCA log-likelihood `∑ n, log N(xₙ | μ, W Wᵀ + σ² I)` of data `xs`. -/
noncomputable def logLik (xs : Fin N → EuclideanSpace ℝ (Fin d)) (μ : EuclideanSpace ℝ (Fin d))
    (W : Matrix (Fin d) (Fin q) ℝ) (σ2 : ℝ) : ℝ :=
  ∑ n, log (multivariateGaussianPDFReal μ (ppcaCov W σ2) (xs n))

/-- The sample mean. -/
noncomputable abbrev sampleMean (xs : Fin N → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  weightedMean 1 xs

/-- The sample covariance `(1 / N) ∑ n, (xₙ - x̄)(xₙ - x̄)ᵀ`. -/
noncomputable abbrev sampleCov (xs : Fin N → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  weightedScatter 1 xs (sampleMean xs)

/-- With no data the log-likelihood is zero. -/
theorem logLik_of_N_eq_zero (hN : N = 0) (xs : Fin N → EuclideanSpace ℝ (Fin d))
    (μ : EuclideanSpace ℝ (Fin d)) (W : Matrix (Fin d) (Fin q) ℝ) (σ2 : ℝ) :
    logLik xs μ W σ2 = 0 := by
  subst hN
  simp [logLik]

/-- **The mean MLE is the sample mean**, for any loading matrix `W` and `σ² > 0`. -/
theorem logLik_le_sampleMean (xs : Fin N → EuclideanSpace ℝ (Fin d))
    (μ : EuclideanSpace ℝ (Fin d)) (W : Matrix (Fin d) (Fin q) ℝ) {σ2 : ℝ} (hσ : 0 < σ2) :
    logLik xs μ W σ2 ≤ logLik xs (sampleMean xs) W σ2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · rw [logLik_of_N_eq_zero hN, logLik_of_N_eq_zero hN]
  have hw : 0 < ∑ n, (1 : Fin N → ℝ) n := by simp [hN]
  simpa [logLik] using
    sum_mul_log_multivariateGaussianPDFReal_le_weightedMean hw xs μ (ppcaCov_posDef W hσ)

/-- **The probabilistic PCA likelihood is at most the unconstrained Gaussian maximum**: when the
sample covariance is positive definite (for example, data not all in an affine hyperplane,
`weightedScatter_posDef`), every `(μ, W, σ²)` has log-likelihood at most that of the Gaussian with
the sample mean and the sample covariance. -/
theorem logLik_le_gaussianMLE {xs : Fin N → EuclideanSpace ℝ (Fin d)}
    (hS : (sampleCov xs).PosDef) (μ : EuclideanSpace ℝ (Fin d)) (W : Matrix (Fin d) (Fin q) ℝ)
    {σ2 : ℝ} (hσ : 0 < σ2) :
    logLik xs μ W σ2 ≤
      ∑ n, log (multivariateGaussianPDFReal (sampleMean xs) (sampleCov xs) (xs n)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [logLik]
  have hw : 0 < ∑ n, (1 : Fin N → ℝ) n := by simp [hN]
  simpa [logLik] using sum_mul_log_multivariateGaussianPDFReal_le_of_posDef hw hS μ
    (ppcaCov_posDef W hσ)

/-- `(μ₀, W₀, σ₀²)` is a probabilistic PCA maximum-likelihood estimate: a valid parameter
(`σ₀² > 0`) whose log-likelihood is at least that of every valid parameter `(μ, W, σ² > 0)`. -/
def IsMLE (xs : Fin N → EuclideanSpace ℝ (Fin d)) (μ₀ : EuclideanSpace ℝ (Fin d))
    (W₀ : Matrix (Fin d) (Fin q) ℝ) (σ₀2 : ℝ) : Prop :=
  0 < σ₀2 ∧ ∀ (μ : EuclideanSpace ℝ (Fin d)) (W : Matrix (Fin d) (Fin q) ℝ) (σ2 : ℝ), 0 < σ2 →
    logLik xs μ W σ2 ≤ logLik xs μ₀ W₀ σ₀2

/-- **Exact recovery**: if the sample covariance has the probabilistic PCA form `W₀ W₀ᵀ + σ₀² I`
with `σ₀² > 0`, then `(x̄, W₀, σ₀²)` is a maximum-likelihood estimate. -/
theorem isMLE_of_sampleCov_eq {xs : Fin N → EuclideanSpace ℝ (Fin d)}
    {W₀ : Matrix (Fin d) (Fin q) ℝ} {σ₀2 : ℝ} (hσ₀ : 0 < σ₀2)
    (h : sampleCov xs = ppcaCov W₀ σ₀2) : IsMLE xs (sampleMean xs) W₀ σ₀2 := by
  refine ⟨hσ₀, fun μ W σ2 hσ => ?_⟩
  have := logLik_le_gaussianMLE (h ▸ ppcaCov_posDef W₀ hσ₀) μ W hσ
  rwa [h] at this

/-- **No latent factors (`W = 0`): the noise-variance MLE is `tr S / d`**, the average sample
variance (Tipping and Bishop's `σ²` estimate with no retained components). -/
theorem logLik_zero_le {xs : Fin N → EuclideanSpace ℝ (Fin d)}
    (hT : 0 < (sampleCov xs).trace) (μ : EuclideanSpace ℝ (Fin d)) {σ2 : ℝ} (hσ : 0 < σ2) :
    logLik xs μ (0 : Matrix (Fin d) (Fin q) ℝ) σ2 ≤
      logLik xs (sampleMean xs) (0 : Matrix (Fin d) (Fin q) ℝ) ((sampleCov xs).trace / d) := by
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by subst h; simp [weightedScatter] at hT
  have hw : 0 < ∑ n, (1 : Fin N → ℝ) n := by simp [hN]
  have hd : 0 < d := Nat.pos_of_ne_zero fun h => by subst h; simp at hT
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set T := (sampleCov xs).trace with hTdef
  have hTpos : 0 < T := hT
  have hs : 0 < T / d := div_pos hTpos hd'
  -- the log-likelihood of `N(x̄, s I)`
  have hcov : ∀ s : ℝ, ppcaCov (0 : Matrix (Fin d) (Fin q) ℝ) s = s • 1 := fun s => by
    simp [ppcaCov]
  have hval : ∀ {s : ℝ}, 0 < s → logLik xs (sampleMean xs) (0 : Matrix (Fin d) (Fin q) ℝ) s =
      -((N : ℝ) / 2) * (d * log (2 * π) + d * log s + T / s) := by
    intro s hs
    have hinv : (s • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = s⁻¹ • 1 :=
      inv_eq_left_inv (by rw [smul_mul_smul, Matrix.one_mul, inv_mul_cancel₀ hs.ne', one_smul])
    have h := sum_mul_log_multivariateGaussianPDFReal_eq hw.ne' xs (sampleMean xs)
      (ppcaCov_posDef (0 : Matrix (Fin d) (Fin q) ℝ) hs)
    simp only [Pi.one_apply, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at h
    rw [logLik, h, hcov, hinv, det_smul, det_one, mul_one, Fintype.card_fin, log_pow,
      Matrix.smul_mul, Matrix.one_mul, trace_smul, smul_eq_mul, ← hTdef]
    ring
  refine (logLik_le_sampleMean xs μ _ hσ).trans ?_
  rw [hval hσ, hval hs]
  -- `d log s + T / s ≥ d log (T / d) + d`
  have hlog := log_le_sub_one_of_pos (div_pos hTpos (mul_pos hd' hσ))
  rw [log_div hTpos.ne' (mul_pos hd' hσ).ne', log_mul hd'.ne' hσ.ne'] at hlog
  have e2 : T / (T / d) = d := by field_simp
  rw [log_div hTpos.ne' hd'.ne', e2]
  have hN' : (0 : ℝ) ≤ N / 2 := by positivity
  have key : d * (log T - log d) + d ≤ d * log σ2 + T / σ2 := by
    have := mul_le_mul_of_nonneg_left hlog hd'.le
    have e : d * (T / (d * σ2) - 1) = T / σ2 - d := by field_simp
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left key hN']

end Cslib.MachineLearning.LatentVariable.ProbabilisticPCA
