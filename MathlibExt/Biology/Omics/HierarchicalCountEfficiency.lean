/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Omics.HierarchicalCountMLE
public import MathlibExt.Probability.Statistics.VectorInference
public import MathlibExt.Probability.Statistics.GodambeInequality
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Asymptotic normality and efficiency of the joint count MLE

`MathlibExt.Biology.Omics.HierarchicalCount` models a count `k` at size factor `σ > 0` as
`k ∣ λ ~ Po(σ λ)`, `λ ~ Gamma(a, b)`, with negative binomial marginal law
`marginalLik a b σ = NB(a, σ a / b)`, and estimates `(a, b)` by the method of moments;
`MathlibExt.Biology.Omics.HierarchicalCountMLE` writes the score equations of the joint
(type-II) maximum-likelihood estimator and proves a consistent root exists. This file compares the
two estimators to first order at a common size factor `σ`: it computes the Fisher information
of one count, proves asymptotic normality of consistent roots of the joint score equations and of
the moment estimator, and proves that the asymptotic covariance of the moment estimator dominates
the inverse Fisher information.

The hyperparameter is a vector `θ = (a, b) ∈ EuclideanSpace ℝ (Fin 2)` (shape `θ 0`, rate `θ 1`).

## Main definitions

* `countScore σ θ k`: the per-count score `(∑_{j<k} 1/(a+j) + log b - log (b+σ),
  a/b - (a+k)/(b+σ))`; it is the gradient of `log (marginalLik a b σ k)`
  (`score_marginalLik_eq_countScore`) and sums to `(shapeScore, rateScore)` (`sum_countScore`).
* `trigammaIncrement a k = ∑_{j<k} 1/(a+j)²`; `countHessian σ θ k`: the derivative of the score.
* `countFisherInfo a b σ τ`: the Fisher information
  `[[τ, -σ/(b(b+σ))], [-σ/(b(b+σ)), aσ/(b²(b+σ))]]`, `τ = E[trigammaIncrement a K]`.
* `momEstFun σ θ k = (b k - σ a, b² k² - σ a b - σ² a - σ² a²)`: the moment equations as an
  estimating function; `momEstDeriv` its derivative; `momJacobian a b σ` its expected derivative.
* `momEstimator σ X n`: the moment estimate `(momShape M̂ₙ V̂ₙ, momRate σ M̂ₙ V̂ₙ)`.

## Main results

* Fisher information: `integral_countHessian` (the expected score derivative is
  `-countFisherInfo` when the count mean is `σ a / b`), `inner_countFisherInfo_self_pos` and
  `isUnit_countFisherInfo` (positive definite iff `τ > σ / (a (b + σ))`).
* `tendstoInDistribution_countMLE`: a consistent sequence of roots of the joint score equations
  satisfies `√n (θhat n - θ₀) → I⁻¹ N(0, E[ψ ψᵀ])`; `tendstoInDistribution_countMLE_of_info`:
  the limit is `N(0, I⁻¹)` under the information identity.
* `tendstoInDistribution_mom`: `√n (momEstimator σ X n - θ₀) → -J⁻¹ N(0, E[g gᵀ])`, with no root
  or consistency hypothesis (`sum_momEstFun_mom_eq_zero`, the strong law, and
  `tendsto_mom_of_tendsto`).
* `inner_inverse_countFisherInfo_le` and `variance_inner_countMLE_limit_le`: in every direction
  `u`, `⟪I⁻¹ u, u⟫ ≤ E ⟪g, (J⁻¹)ᵀ u⟫²`, i.e. the variance of every projection of the MLE limit is
  at most that of the moment-estimator limit. This applies Godambe's information inequality
  for estimating functions (`GodambeInequality.inner_inverse_le_integral_inner_sq`).

Source receipt: Cramér, *Mathematical Methods of Statistics* (1946), §33.3, and Lehmann and
Casella, *Theory of Point Estimation* (1998), Theorem 6.5.1 (asymptotic normality of consistent
roots of the likelihood equations), through van der Vaart, *Asymptotic Statistics* (1998),
Theorem 5.41 (Z-estimators,
`VectorInference.tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation`);
Godambe (1960) (information inequality); Fisher (1941) and Anscombe (1950) (efficiency of the
moment estimator of the negative binomial).

## Hypotheses, and what is not proved here

The count law is a general probability measure `μX` on `ℕ`; as in `HierarchicalCountMLE`, the law
of a random count is not formalized, so the negative binomial enters through moment and score
hypotheses at the true `θ₀ = (a, b)`:

* **Score equations at the truth** `E[countScore σ θ₀ K] = 0` (hypothesis `hscore`). Its rate
  component is `HierarchicalCountMLE.hasSum_rateScore_term_mul_marginalLik`; its shape component
  (`E[∑_{j<K} 1/(a+j)] = log (1 + σ/b)`) is not proved anywhere in the library.
* **Profile information** `τ > σ / (a (b + σ))` (hypothesis `hτ`), equivalent to positive
  definiteness of the information; not derived for the negative binomial.
* **Information identity** `⟪I z, z⟫ = E ⟪ψ, z⟫²` and **differentiated unbiasedness of the moment
  equations** `⟪J x, w⟫ = -E[⟪ψ, x⟫ ⟪g, w⟫]` (hypotheses `hinfo`, `hunb` of the efficiency
  results): both are differentiation under the expectation of `∑ₖ P(k ∣ θ) = 1` and
  `∑ₖ P(k ∣ θ) g(θ, k) = 0`, which is not carried out here.
* **Roots and consistency of the MLE** (`hroot`, `hcons`) are hypotheses, as in `VectorInference`.
  `HierarchicalCountMLE.ae_eventually_exists_score_root` gives roots that exist and converge
  almost surely, but no measurable selection of them, so it is not bridged here.
* **Moments.** The theorems assume a finite second (MLE) or fourth (moment estimator) moment and,
  where needed, the negative binomial mean `σ a / b` and second moment; these are proved for
  `marginalLik` (`ProbabilityTheory.hasSum_mul_negBinomialReal`,
  `ProbabilityTheory.hasSum_sq_negBinomialReal`), but the fourth moment is not.
* Strictness of the efficiency loss, heterogeneous size factors, and the global-maximizer
  property of the root are not addressed.

## Implementation notes

Reuse search (2026-11-12, `MathlibExt`, `CSLibExt`, `WantedExt`: Fisher information,
Cramér–Rao, Godambe, sandwich, asymptotic normality, efficiency, negative binomial): the
Z-estimator theorem, `apply_inverse_apply`, `inverse_apply_apply`, `inner_inverse_comm` and
`isUnit_of_inner_self_pos` come from `VectorInference`; the shape/rate scores, the digamma
increment and the closed form `log_marginalLik_eq` from `HierarchicalCountMLE`; `momShape`,
`momRate`, `sampleMean`, `sampleVar`, `eq_mom_of_moment_equations` and `tendsto_mom_of_tendsto`
from `HierarchicalCount`; the strong law is Mathlib's `strong_law_ae`. No Godambe/estimating-
function information inequality existed; `VectorInference.cramerRao` is the unbiased-estimator
bound, a different statement. The general inequality (any measure, any real inner product
space) is `MathlibExt.Probability.Statistics.GodambeInequality.inner_inverse_le_integral_inner_sq`,
in its own statistics module. The 2×2 operators are `Matrix.toEuclideanCLM`.

## References

* F. J. Anscombe, *Sampling theory of the negative binomial and logarithmic series
  distributions*, Biometrika 37 (1950), 358–382.
* H. Cramér, *Mathematical Methods of Statistics*, Princeton University Press, 1946.
* R. A. Fisher, *The negative binomial distribution*, Ann. Eugenics 11 (1941), 182–187.
* V. P. Godambe, *An optimum property of regular maximum likelihood estimation*, Ann. Math.
  Statist. 31 (1960), 1208–1211.
* E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed., Springer, 1998.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology Finset Function
open scoped RealInnerProductSpace
open MathlibExt.Probability.Statistics.VectorInference
  (tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation apply_inverse_apply
    inverse_apply_apply inner_inverse_comm isUnit_of_inner_self_pos)
open MathlibExt.Probability.Statistics.GodambeInequality
  (integrable_inner_smul inner_inverse_le_integral_inner_sq)

namespace MathlibExt.Biology.Omics.HierarchicalCount

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-! ### The per-count score and its derivative -/

/-- The score of one count `k` at size factor `σ` in the hyperparameter `θ = (a, b)` (prior
shape `θ 0`, prior rate `θ 1`): the gradient
`(∑_{j<k} 1 / (a + j) + log b - log (b + σ), a / b - (a + k) / (b + σ))` of
`log (marginalLik a b σ k)`. Summed over a sample it is `(shapeScore, rateScore)`
(`sum_countScore`). -/
noncomputable def countScore (σ : ℝ) (θ : E₂) (k : ℕ) : E₂ :=
  !₂[digammaIncrement (θ 0) k + log (θ 1) - log (θ 1 + σ), θ 0 / θ 1 - (θ 0 + k) / (θ 1 + σ)]

/-- The trigamma increment `∑_{j<k} 1 / (a + j)²`, equal to `ψ'(a) - ψ'(a + k)` for `a > 0`; it is
minus the derivative of `digammaIncrement a k` in `a`. -/
noncomputable def trigammaIncrement (a : ℝ) (k : ℕ) : ℝ := ∑ j ∈ range k, ((a + j) ^ 2)⁻¹

/-- The derivative of `countScore σ · k` at `θ = (a, b)` (the Hessian of the log marginal
likelihood of one count), as the operator of the symmetric matrix
`[[-∑_{j<k} 1/(a+j)², 1/b - 1/(b+σ)], [1/b - 1/(b+σ), (a+k)/(b+σ)² - a/b²]]`. -/
noncomputable def countHessian (σ : ℝ) (θ : E₂) (k : ℕ) : E₂ →L[ℝ] E₂ :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) !![-trigammaIncrement (θ 0) k, (θ 1)⁻¹ - (θ 1 + σ)⁻¹;
    (θ 1)⁻¹ - (θ 1 + σ)⁻¹, (θ 0 + k) / (θ 1 + σ) ^ 2 - θ 0 / θ 1 ^ 2]

/-- The shape component of the per-count score. -/
theorem countScore_apply_zero (σ : ℝ) (θ : E₂) (k : ℕ) :
    countScore σ θ k 0 = digammaIncrement (θ 0) k + log (θ 1) - log (θ 1 + σ) := rfl

/-- The rate component of the per-count score. -/
theorem countScore_apply_one (σ : ℝ) (θ : E₂) (k : ℕ) :
    countScore σ θ k 1 = θ 0 / θ 1 - (θ 0 + k) / (θ 1 + σ) := rfl

/-- Summed over a sample with a common size factor `σ`, the per-count scores are the shape and
rate scores of `HierarchicalCountMLE`. -/
theorem sum_countScore {ι : Type*} [Fintype ι] (σ : ℝ) (θ : E₂) (k : ι → ℕ) :
    ∑ i, countScore σ θ (k i) =
      !₂[shapeScore (θ 0) (θ 1) (fun _ => σ) k, rateScore (θ 0) (θ 1) (fun _ => σ) k] := by
  ext j
  fin_cases j <;> simp [countScore, shapeScore, rateScore, WithLp.ofLp_sum, Finset.sum_apply]

private lemma hasDerivAt_digammaIncrement {a : ℝ} (ha : 0 < a) (k : ℕ) :
    HasDerivAt (fun x => digammaIncrement x k) (-trigammaIncrement a k) a := by
  unfold digammaIncrement trigammaIncrement
  rw [← sum_neg_distrib]
  refine HasDerivAt.fun_sum fun j _ => ?_
  have h := ((hasDerivAt_id' a).add_const (j : ℝ)).inv (by positivity)
  convert h using 1
  field_simp

private lemma hasFDerivAt_toLp_two {f g : E₂ → ℝ} {f' g' : E₂ →L[ℝ] ℝ} {θ : E₂}
    (hf : HasFDerivAt f f' θ) (hg : HasFDerivAt g g' θ) :
    HasFDerivAt (fun t => !₂[f t, g t])
      (f'.smulRight (EuclideanSpace.single 0 1) + g'.smulRight (EuclideanSpace.single 1 1)) θ := by
  have h := (hf.smul_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))).add
    (hg.smul_const (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
  convert h using 1
  funext t
  ext i
  fin_cases i <;> simp

/-- **Score derivative.** For `a, b > 0` and `σ ≥ 0`, `countScore σ · k` is differentiable at
`θ = (a, b)` with derivative `countHessian σ θ k`. -/
theorem hasFDerivAt_countScore {σ : ℝ} (hσ : 0 ≤ σ) {θ : E₂} (ha : 0 < θ 0) (hb : 0 < θ 1)
    (k : ℕ) : HasFDerivAt (fun t => countScore σ t k) (countHessian σ θ k) θ := by
  have hb' : 0 < θ 1 + σ := by linarith
  have hp0 : HasFDerivAt (fun t : E₂ => t 0) (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) θ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt
  have hp1 : HasFDerivAt (fun t : E₂ => t 1) (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) θ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
  have hf := (((hasDerivAt_digammaIncrement ha k).comp_hasFDerivAt θ hp0).add
    (hp1.log hb.ne')).sub ((hp1.add_const σ).log hb'.ne')
  have hi1 : HasFDerivAt (fun t : E₂ => (t 1)⁻¹) ((-((θ 1) ^ 2)⁻¹) • EuclideanSpace.proj (𝕜 := ℝ)
      (1 : Fin 2)) θ := (hasDerivAt_inv hb.ne').comp_hasFDerivAt θ hp1
  have hi2 : HasFDerivAt (fun t : E₂ => (t 1 + σ)⁻¹) ((-((θ 1 + σ) ^ 2)⁻¹) •
      EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) θ :=
    (hasDerivAt_inv hb'.ne').comp_hasFDerivAt θ (hp1.add_const σ)
  have hg := (hp0.mul hi1).sub ((hp0.add_const (k : ℝ)).mul hi2)
  convert hasFDerivAt_toLp_two hf hg using 1
  · funext t
    simp [countScore, div_eq_mul_inv]
  · ext v i
    fin_cases i
    · simp [countHessian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    · simp [countHessian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
      ring

/-- **`countScore` is the score of the marginal likelihood.** For `σ > 0` and `θ` with positive
coordinates, `countScore σ θ k` is the gradient at `θ` of `t ↦ log (marginalLik (t 0) (t 1) σ k)`,
the score (`VectorInference.score`) of the negative binomial marginal family in `(a, b)`. -/
theorem score_marginalLik_eq_countScore {σ : ℝ} (hσ : 0 < σ) {θ : E₂} (ha : 0 < θ 0)
    (hb : 0 < θ 1) (k : ℕ) :
    MathlibExt.Probability.Statistics.VectorInference.score
      (fun (t : E₂) (j : ℕ) => marginalLik (t 0) (t 1) σ j) θ k = countScore σ θ k := by
  have hB : 0 < θ 1 + σ := by linarith
  have hp0 : HasFDerivAt (fun t : E₂ => t 0) (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) θ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt
  have hp1 : HasFDerivAt (fun t : E₂ => t 1) (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) θ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
  have h1 : HasFDerivAt (fun t : E₂ => ∑ j ∈ range k, log (t 0 + j))
      (digammaIncrement (θ 0) k • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) θ := by
    rw [digammaIncrement, Finset.sum_smul]
    exact HasFDerivAt.fun_sum fun j _ => (hp0.add_const (j : ℝ)).log (by positivity)
  have h2 := hp0.mul (hp1.log hb.ne')
  have h3 := (hp0.add_const (k : ℝ)).mul ((hp1.add_const σ).log hB.ne')
  have hF := (((h1.add_const ((k : ℝ) * log σ)).sub_const (log (k.factorial : ℝ))).add h2).sub h3
  have hG : HasGradientAt (fun t : E₂ => log (marginalLik (t 0) (t 1) σ k)) (countScore σ θ k)
      θ := by
    rw [hasGradientAt_iff_hasFDerivAt]
    refine (hF.congr_fderiv ?_).congr_of_eventuallyEq ?_
    · ext v
      simp [countScore, PiLp.inner_apply, Fin.sum_univ_two]
      field_simp
      ring
    · have o0 : {t : E₂ | 0 < t 0} ∈ 𝓝 θ :=
        (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous).mem_nhds
          ha
      have o1 : {t : E₂ | 0 < t 1} ∈ 𝓝 θ :=
        (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous).mem_nhds
          hb
      filter_upwards [o0, o1] with t h0 h1'
      exact log_marginalLik_eq h0 h1' hσ k
  exact hG.gradient

/-! ### Lipschitz envelope of the score derivative -/

private lemma norm_le_abs_add_abs (x : E₂) : ‖x‖ ≤ |x 0| + |x 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [abs_nonneg (x 0), abs_nonneg (x 1), sq_abs (x 0), sq_abs (x 1)]

private lemma abs_apply_le_norm (x : E₂) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  simpa using PiLp.norm_apply_le x i

private lemma norm_toEuclideanCLM_le (p q r s : ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) !![p, q; r, s]‖ ≤ |p| + |q| + |r| + |s| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  refine (norm_le_abs_add_abs _).trans ?_
  have h0 := abs_apply_le_norm v 0
  have h1 := abs_apply_le_norm v 1
  have e0 : (Matrix.toEuclideanCLM (𝕜 := ℝ) !![p, q; r, s] v) 0 = p * v 0 + q * v 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have e1 : (Matrix.toEuclideanCLM (𝕜 := ℝ) !![p, q; r, s] v) 1 = r * v 0 + s * v 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [e0, e1]
  have k1 := abs_add_le (p * v 0) (q * v 1)
  have k2 := abs_add_le (r * v 0) (s * v 1)
  rw [abs_mul, abs_mul] at k1 k2
  have m1 := mul_le_mul_of_nonneg_left h0 (abs_nonneg p)
  have m2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg q)
  have m3 := mul_le_mul_of_nonneg_left h0 (abs_nonneg r)
  have m4 := mul_le_mul_of_nonneg_left h1 (abs_nonneg s)
  nlinarith

private lemma abs_inv_sub_inv_le {x y c : ℝ} (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y) :
    |x⁻¹ - y⁻¹| ≤ |x - y| / c ^ 2 := by
  have hx0 : 0 < x := hc.trans_le hx
  have hy0 : 0 < y := hc.trans_le hy
  rw [inv_sub_inv hx0.ne' hy0.ne', abs_div, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by nlinarith)

private lemma abs_inv_sq_sub_inv_sq_le {x y c : ℝ} (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y) :
    |(x ^ 2)⁻¹ - (y ^ 2)⁻¹| ≤ 2 * |x - y| / c ^ 3 := by
  have hx0 : 0 < x := hc.trans_le hx
  have hy0 : 0 < y := hc.trans_le hy
  have hxi : x⁻¹ ≤ c⁻¹ := inv_anti₀ hc hx
  have hyi : y⁻¹ ≤ c⁻¹ := inv_anti₀ hc hy
  have e : (x ^ 2)⁻¹ - (y ^ 2)⁻¹ = (x⁻¹ - y⁻¹) * (x⁻¹ + y⁻¹) := by ring
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < x⁻¹ + y⁻¹)]
  calc |x⁻¹ - y⁻¹| * (x⁻¹ + y⁻¹) ≤ (|x - y| / c ^ 2) * (2 * c⁻¹) :=
        mul_le_mul (abs_inv_sub_inv_le hc hx hy) (by linarith) (by positivity) (by positivity)
    _ = 2 * |x - y| / c ^ 3 := by field_simp

private lemma inv_sq_le {x c : ℝ} (hc : 0 < c) (hx : c ≤ x) : (x ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ :=
  inv_anti₀ (by positivity) (pow_le_pow_left₀ hc.le hx 2)

/-- **Lipschitz envelope of the score derivative.** If both coordinates of `θ` and of `θ₀` are at
least `c > 0` and `σ ≥ 0`, then
`‖countHessian σ θ k - countHessian σ θ₀ k‖ ≤ (6 / c² + 4 (|θ₀ 0| + k) / c³) ‖θ - θ₀‖`;
the envelope is affine in the count `k`. -/
theorem norm_countHessian_sub_le {σ : ℝ} (hσ : 0 ≤ σ) {θ₀ θ : E₂} {c : ℝ} (hc : 0 < c)
    (ha : c ≤ θ 0) (hb : c ≤ θ 1) (ha₀ : c ≤ θ₀ 0) (hb₀ : c ≤ θ₀ 1) (k : ℕ) :
    ‖countHessian σ θ k - countHessian σ θ₀ k‖ ≤
      (6 / c ^ 2 + 4 * (|θ₀ 0| + k) / c ^ 3) * ‖θ - θ₀‖ := by
  set r := ‖θ - θ₀‖ with hr
  have hra : |θ 0 - θ₀ 0| ≤ r := by simpa using abs_apply_le_norm (θ - θ₀) 0
  have hrb : |θ 1 - θ₀ 1| ≤ r := by simpa using abs_apply_le_norm (θ - θ₀) 1
  have hr0 : 0 ≤ r := norm_nonneg _
  set a := θ 0
  set b := θ 1
  set a₀ := θ₀ 0
  set b₀ := θ₀ 1
  have hB : c ≤ b + σ := by linarith
  have hB₀ : c ≤ b₀ + σ := by linarith
  -- entrywise bounds
  have h00 : |-trigammaIncrement a k - -trigammaIncrement a₀ k| ≤ 2 * k * r / c ^ 3 := by
    rw [neg_sub_neg, abs_sub_comm, trigammaIncrement, trigammaIncrement, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ range k, |((a + j) ^ 2)⁻¹ - ((a₀ + j) ^ 2)⁻¹|
        ≤ ∑ j ∈ range k, 2 * r / c ^ 3 := by
          refine sum_le_sum fun j _ => ?_
          have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          refine (abs_inv_sq_sub_inv_sq_le hc (by linarith) (by linarith)).trans ?_
          rw [add_sub_add_right_eq_sub]
          gcongr
      _ = 2 * k * r / c ^ 3 := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have h01 : |(b⁻¹ - (b + σ)⁻¹) - (b₀⁻¹ - (b₀ + σ)⁻¹)| ≤ 2 * r / c ^ 2 := by
    have e1 := abs_inv_sub_inv_le hc hb hb₀
    have e2 := abs_inv_sub_inv_le hc hB hB₀
    rw [add_sub_add_right_eq_sub] at e2
    have e3 : |b - b₀| / c ^ 2 ≤ r / c ^ 2 := by gcongr
    calc _ = |(b⁻¹ - b₀⁻¹) - ((b + σ)⁻¹ - (b₀ + σ)⁻¹)| := by ring_nf
      _ ≤ |b⁻¹ - b₀⁻¹| + |(b + σ)⁻¹ - (b₀ + σ)⁻¹| := abs_sub _ _
      _ ≤ 2 * r / c ^ 2 := by rw [mul_div_assoc]; linarith
  have h11 : |((a + k) / (b + σ) ^ 2 - a / b ^ 2) - ((a₀ + k) / (b₀ + σ) ^ 2 - a₀ / b₀ ^ 2)| ≤
      (2 / c ^ 2 + (4 * |a₀| + 2 * k) / c ^ 3) * r := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have e1 := abs_inv_sq_sub_inv_sq_le hc hB hB₀
    have e2 := abs_inv_sq_sub_inv_sq_le hc hb hb₀
    rw [add_sub_add_right_eq_sub] at e1
    have i1 := inv_sq_le hc hB
    have i2 := inv_sq_le hc hb
    have p1 : 0 ≤ ((b + σ) ^ 2)⁻¹ := by positivity
    have p2 : 0 ≤ (b ^ 2)⁻¹ := by positivity
    have eq : ((a + k) / (b + σ) ^ 2 - a / b ^ 2) - ((a₀ + k) / (b₀ + σ) ^ 2 - a₀ / b₀ ^ 2) =
        (a - a₀) * ((b + σ) ^ 2)⁻¹ + (a₀ + k) * (((b + σ) ^ 2)⁻¹ - ((b₀ + σ) ^ 2)⁻¹) -
          (a - a₀) * (b ^ 2)⁻¹ - a₀ * ((b ^ 2)⁻¹ - (b₀ ^ 2)⁻¹) := by ring
    rw [eq]
    have t1 : |(a - a₀) * ((b + σ) ^ 2)⁻¹| ≤ r * (c ^ 2)⁻¹ := by
      rw [abs_mul, abs_of_nonneg p1]; exact mul_le_mul hra i1 p1 hr0
    have t2 : |(a₀ + k) * (((b + σ) ^ 2)⁻¹ - ((b₀ + σ) ^ 2)⁻¹)| ≤ (|a₀| + k) * (2 * r / c ^ 3) := by
      rw [abs_mul]
      refine mul_le_mul ((abs_add_le _ _).trans (by rw [Nat.abs_cast])) (e1.trans ?_)
        (abs_nonneg _) (by positivity)
      gcongr
    have t3 : |(a - a₀) * (b ^ 2)⁻¹| ≤ r * (c ^ 2)⁻¹ := by
      rw [abs_mul, abs_of_nonneg p2]; exact mul_le_mul hra i2 p2 hr0
    have t4 : |a₀ * ((b ^ 2)⁻¹ - (b₀ ^ 2)⁻¹)| ≤ |a₀| * (2 * r / c ^ 3) := by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left (e2.trans ?_) (abs_nonneg _)
      gcongr
    have tri : |(a - a₀) * ((b + σ) ^ 2)⁻¹ + (a₀ + k) * (((b + σ) ^ 2)⁻¹ - ((b₀ + σ) ^ 2)⁻¹) -
        (a - a₀) * (b ^ 2)⁻¹ - a₀ * ((b ^ 2)⁻¹ - (b₀ ^ 2)⁻¹)| ≤
        |(a - a₀) * ((b + σ) ^ 2)⁻¹| + |(a₀ + k) * (((b + σ) ^ 2)⁻¹ - ((b₀ + σ) ^ 2)⁻¹)| +
          |(a - a₀) * (b ^ 2)⁻¹| + |a₀ * ((b ^ 2)⁻¹ - (b₀ ^ 2)⁻¹)| := by
      refine (abs_sub _ _).trans ?_
      gcongr
      refine (abs_sub _ _).trans ?_
      gcongr
      exact abs_add_le _ _
    refine tri.trans ?_
    have : (2 / c ^ 2 + (4 * |a₀| + 2 * k) / c ^ 3) * r =
        r * (c ^ 2)⁻¹ + (|a₀| + k) * (2 * r / c ^ 3) + r * (c ^ 2)⁻¹ + |a₀| * (2 * r / c ^ 3) := by
      field_simp; ring
    rw [this]
    linarith
  have hsub : countHessian σ θ k - countHessian σ θ₀ k =
      Matrix.toEuclideanCLM (𝕜 := ℝ) !![-trigammaIncrement a k - -trigammaIncrement a₀ k,
        (b⁻¹ - (b + σ)⁻¹) - (b₀⁻¹ - (b₀ + σ)⁻¹); (b⁻¹ - (b + σ)⁻¹) - (b₀⁻¹ - (b₀ + σ)⁻¹),
        ((a + k) / (b + σ) ^ 2 - a / b ^ 2) - ((a₀ + k) / (b₀ + σ) ^ 2 - a₀ / b₀ ^ 2)] := by
    rw [countHessian, countHessian, ← map_sub]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hsub]
  refine (norm_toEuclideanCLM_le _ _ _ _).trans ?_
  have : (6 / c ^ 2 + 4 * (|a₀| + k) / c ^ 3) * r =
      2 * k * r / c ^ 3 + 2 * r / c ^ 2 + 2 * r / c ^ 2 +
        (2 / c ^ 2 + (4 * |a₀| + 2 * k) / c ^ 3) * r := by
    field_simp; ring
  rw [this]
  linarith

/-! ### Fisher information of one count -/

/-- The Fisher information matrix of one count at size factor `σ` and hyperparameter `(a, b)`,
`[[τ, -σ / (b (b + σ))], [-σ / (b (b + σ)), a σ / (b² (b + σ))]]`, as an operator, with the shape
entry `τ = E[∑_{j<K} 1 / (a + j)²]` (an expected trigamma increment, which has no closed form)
supplied as a parameter. `integral_countHessian`: it is minus the expected score derivative. -/
noncomputable def countFisherInfo (a b σ τ : ℝ) : E₂ →L[ℝ] E₂ :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) !![τ, -(σ / (b * (b + σ))); -(σ / (b * (b + σ))),
    a * σ / (b ^ 2 * (b + σ))]

/-- The bilinear form of the Fisher information in coordinates. -/
theorem inner_countFisherInfo (a b σ τ : ℝ) (u v : E₂) :
    ⟪countFisherInfo a b σ τ u, v⟫ = τ * u 0 * v 0 - σ / (b * (b + σ)) * (u 0 * v 1 + u 1 * v 0) +
      a * σ / (b ^ 2 * (b + σ)) * u 1 * v 1 := by
  rw [real_inner_comm, countFisherInfo, Matrix.inner_toEuclideanCLM]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The Fisher information is symmetric. -/
theorem inner_countFisherInfo_comm (a b σ τ : ℝ) (u v : E₂) :
    ⟪countFisherInfo a b σ τ u, v⟫ = ⟪u, countFisherInfo a b σ τ v⟫ := by
  rw [inner_countFisherInfo, real_inner_comm, inner_countFisherInfo]
  ring

/-- **Positive definiteness.** For `a, b, σ > 0`, the Fisher information is positive definite as
soon as the shape entry exceeds `σ / (a (b + σ))`; this is positivity of the profile information
for the shape, `τ - σ / (a (b + σ)) > 0`. -/
theorem inner_countFisherInfo_self_pos {a b σ τ : ℝ} (ha : 0 < a) (hb : 0 < b) (hσ : 0 < σ)
    (hτ : σ / (a * (b + σ)) < τ) {u : E₂} (hu : u ≠ 0) :
    0 < ⟪countFisherInfo a b σ τ u, u⟫ := by
  rw [inner_countFisherInfo]
  set c := σ / (b * (b + σ))
  set d := a * σ / (b ^ 2 * (b + σ))
  have hτ0 : 0 < τ := lt_trans (by positivity) hτ
  have hd : 0 < d := by positivity
  have hcd : σ / (a * (b + σ)) * d = c ^ 2 := by
    simp only [c, d]; field_simp
  have hdet : c ^ 2 < τ * d := by rw [← hcd]; exact mul_lt_mul_of_pos_right hτ hd
  have hxy : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    exact hu (by ext i; fin_cases i <;> simp [h.1, h.2])
  have key : 0 < τ * (τ * u 0 * u 0 - c * (u 0 * u 1 + u 1 * u 0) + d * u 1 * u 1) := by
    have e : τ * (τ * u 0 * u 0 - c * (u 0 * u 1 + u 1 * u 0) + d * u 1 * u 1) =
        (τ * u 0 - c * u 1) ^ 2 + (τ * d - c ^ 2) * u 1 ^ 2 := by ring
    rw [e]
    rcases eq_or_ne (u 1) 0 with h1 | h1
    · have h0 : u 0 ≠ 0 := hxy.resolve_right (not_not.2 h1)
      have := lt_of_le_of_ne (sq_nonneg (τ * u 0))
        (Ne.symm (pow_ne_zero 2 (mul_ne_zero hτ0.ne' h0)))
      rw [h1]
      calc 0 < (τ * u 0) ^ 2 := this
        _ = _ := by ring
    · have h1' := lt_of_le_of_ne (sq_nonneg (u 1)) (Ne.symm (pow_ne_zero 2 h1))
      have : 0 < (τ * d - c ^ 2) * u 1 ^ 2 := mul_pos (by linarith) h1'
      linarith [sq_nonneg (τ * u 0 - c * u 1)]
  exact pos_of_mul_pos_right key hτ0.le

/-- The Fisher information is invertible under the profile-information condition. -/
theorem isUnit_countFisherInfo {a b σ τ : ℝ} (ha : 0 < a) (hb : 0 < b) (hσ : 0 < σ)
    (hτ : σ / (a * (b + σ)) < τ) : IsUnit (countFisherInfo a b σ τ) :=
  isUnit_of_inner_self_pos fun _ hu =>
    inner_countFisherInfo_self_pos ha hb hσ hτ hu

private lemma integrable_nat_of_norm_le {F : Type*} [NormedAddCommGroup F]
    {μX : Measure ℕ} [IsFiniteMeasure μX] (hk : Integrable (fun k : ℕ => (k : ℝ)) μX)
    {f : ℕ → F} {A B : ℝ} (h : ∀ k, ‖f k‖ ≤ A + B * k) : Integrable f μX :=
  ((integrable_const A).add (hk.const_mul B)).mono'
    continuous_of_discreteTopology.aestronglyMeasurable (ae_of_all _ h)

private lemma natCast_le_sq (k : ℕ) : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos k with h | h
  · simp [h]
  · have : (1 : ℝ) ≤ k := Nat.one_le_cast.2 h
    nlinarith

private lemma integrable_natCast_of_sq {μX : Measure ℕ} [IsFiniteMeasure μX]
    (hk2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) μX) : Integrable (fun k : ℕ => (k : ℝ)) μX :=
  hk2.mono' continuous_of_discreteTopology.aestronglyMeasurable
    (ae_of_all _ fun k => by rw [norm_eq_abs, Nat.abs_cast]; exact natCast_le_sq k)

private lemma trigammaIncrement_nonneg (a : ℝ) (k : ℕ) : 0 ≤ trigammaIncrement a k :=
  sum_nonneg fun _ _ => by positivity

private lemma trigammaIncrement_le {a : ℝ} (ha : 0 < a) (k : ℕ) :
    trigammaIncrement a k ≤ (a ^ 2)⁻¹ * k := by
  calc trigammaIncrement a k ≤ ∑ _j ∈ range k, (a ^ 2)⁻¹ :=
        sum_le_sum fun j _ => inv_sq_le ha (by simp)
    _ = (a ^ 2)⁻¹ * k := by rw [sum_const, card_range, nsmul_eq_mul, mul_comm]

private lemma integral_toEuclideanCLM {μX : Measure ℕ} [IsProbabilityMeasure μX]
    {f₁ f₂ f₃ f₄ : ℕ → ℝ} (h₁ : Integrable f₁ μX) (h₂ : Integrable f₂ μX) (h₃ : Integrable f₃ μX)
    (h₄ : Integrable f₄ μX) :
    ∫ k, Matrix.toEuclideanCLM (𝕜 := ℝ) !![f₁ k, f₂ k; f₃ k, f₄ k] ∂μX =
      Matrix.toEuclideanCLM (𝕜 := ℝ)
        !![∫ k, f₁ k ∂μX, ∫ k, f₂ k ∂μX; ∫ k, f₃ k ∂μX, ∫ k, f₄ k ∂μX] := by
  set T₁ := Matrix.toEuclideanCLM (𝕜 := ℝ) !![1, 0; 0, 0]
  set T₂ := Matrix.toEuclideanCLM (𝕜 := ℝ) !![0, 1; 0, 0]
  set T₃ := Matrix.toEuclideanCLM (𝕜 := ℝ) !![0, 0; 1, 0]
  set T₄ := Matrix.toEuclideanCLM (𝕜 := ℝ) !![0, 0; 0, 1]
  have h : ∀ p q r t : ℝ, Matrix.toEuclideanCLM (𝕜 := ℝ) !![p, q; r, t] =
      p • T₁ + q • T₂ + r • T₃ + t • T₄ := by
    intro p q r t
    have hm : !![p, q; r, t] = p • !![(1 : ℝ), 0; 0, 0] + q • !![(0 : ℝ), 1; 0, 0] +
        r • !![(0 : ℝ), 0; 1, 0] + t • !![(0 : ℝ), 0; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hm, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
  have hfun : (fun k => Matrix.toEuclideanCLM (𝕜 := ℝ) !![f₁ k, f₂ k; f₃ k, f₄ k]) =
      fun k => f₁ k • T₁ + f₂ k • T₂ + f₃ k • T₃ + f₄ k • T₄ :=
    funext fun k => h _ _ _ _
  have i₁ : Integrable (fun k => f₁ k • T₁) μX := h₁.smul_const _
  have i₂ : Integrable (fun k => f₂ k • T₂) μX := h₂.smul_const _
  have i₃ : Integrable (fun k => f₃ k • T₃) μX := h₃.smul_const _
  have i₄ : Integrable (fun k => f₄ k • T₄) μX := h₄.smul_const _
  rw [hfun, h, integral_add _ i₄, integral_add _ i₃, integral_add i₁ i₂]
  · simp only [integral_smul_const]
  · exact i₁.add i₂
  · exact (i₁.add i₂).add i₃

/-- **Fisher information of one count.** If the count law `μX` has a finite mean equal to the
marginal mean `σ a / b` of the hierarchy, then the expected score derivative at `θ₀ = (a, b)` is
minus `countFisherInfo a b σ τ`, with `τ = E[∑_{j<K} 1 / (a + j)²]`:
`I_ab = -σ / (b (b + σ))`, `I_bb = a σ / (b² (b + σ))`. -/
theorem integral_countHessian {σ : ℝ} {θ₀ : E₂} (ha : 0 < θ₀ 0) (hb : 0 < θ₀ 1) (hσ : 0 ≤ σ)
    {μX : Measure ℕ} [IsProbabilityMeasure μX] (hk : Integrable (fun k : ℕ => (k : ℝ)) μX)
    (hmean : ∫ k, (k : ℝ) ∂μX = σ * θ₀ 0 / θ₀ 1) :
    ∫ k, countHessian σ θ₀ k ∂μX =
      -countFisherInfo (θ₀ 0) (θ₀ 1) σ (∫ k, trigammaIncrement (θ₀ 0) k ∂μX) := by
  have hbs : 0 < θ₀ 1 + σ := by linarith
  have htrig : Integrable (fun k => -trigammaIncrement (θ₀ 0) k) μX :=
    (integrable_nat_of_norm_le hk (A := 0) (B := (θ₀ 0 ^ 2)⁻¹) fun k => by
      rw [norm_eq_abs, abs_of_nonneg (trigammaIncrement_nonneg _ k), zero_add]
      exact trigammaIncrement_le ha k).neg
  have hlin : Integrable (fun k : ℕ => (θ₀ 0 + k) / (θ₀ 1 + σ) ^ 2) μX :=
    ((integrable_const _).add hk).div_const _
  have hbb : Integrable (fun k : ℕ => (θ₀ 0 + k) / (θ₀ 1 + σ) ^ 2 - θ₀ 0 / θ₀ 1 ^ 2) μX :=
    hlin.sub (integrable_const _)
  unfold countHessian
  rw [integral_toEuclideanCLM htrig (integrable_const _) (integrable_const _) hbb, countFisherInfo,
    ← map_neg, integral_const, probReal_univ, one_smul]
  congr 1
  have h2 : ∫ k, ((θ₀ 0 + k) / (θ₀ 1 + σ) ^ 2 - θ₀ 0 / θ₀ 1 ^ 2) ∂μX =
      (θ₀ 0 + σ * θ₀ 0 / θ₀ 1) / (θ₀ 1 + σ) ^ 2 - θ₀ 0 / θ₀ 1 ^ 2 := by
    rw [integral_sub hlin (integrable_const _), integral_div,
      integral_add (integrable_const _) hk, hmean]
    simp
  rw [integral_neg, h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

/-! ### Asymptotic normality of the joint maximum-likelihood root -/

private lemma norm_countScore_le {σ : ℝ} (hσ : 0 ≤ σ) {θ : E₂} (ha : 0 < θ 0) (hb : 0 < θ 1)
    (k : ℕ) : ‖countScore σ θ k‖ ≤
      (|log (θ 1)| + |log (θ 1 + σ)| + θ 0 / θ 1 + θ 0 / (θ 1 + σ)) +
        ((θ 0)⁻¹ + (θ 1 + σ)⁻¹) * k := by
  have hB : 0 < θ 1 + σ := by linarith
  refine (norm_le_abs_add_abs _).trans ?_
  rw [countScore_apply_zero, countScore_apply_one]
  obtain ⟨hd0, hd1⟩ := digammaIncrement_mem_Icc ha k
  have e1 : |digammaIncrement (θ 0) k + log (θ 1) - log (θ 1 + σ)| ≤
      digammaIncrement (θ 0) k + |log (θ 1)| + |log (θ 1 + σ)| := by
    refine (abs_sub _ _).trans ?_
    gcongr
    exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hd0])
  have e2 : |θ 0 / θ 1 - (θ 0 + k) / (θ 1 + σ)| ≤ θ 0 / θ 1 + (θ 0 + k) / (θ 1 + σ) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have e3 : (θ 0 + k) / (θ 1 + σ) = θ 0 / (θ 1 + σ) + (θ 1 + σ)⁻¹ * k := by ring
  have e4 : (k : ℝ) / θ 0 = (θ 0)⁻¹ * k := by ring
  rw [e4] at hd1
  linarith

private lemma norm_countHessian_le {σ : ℝ} (hσ : 0 ≤ σ) {θ : E₂} (ha : 0 < θ 0) (hb : 0 < θ 1)
    (k : ℕ) : ‖countHessian σ θ k‖ ≤
      (2 * ((θ 1)⁻¹ + (θ 1 + σ)⁻¹) + θ 0 / (θ 1 + σ) ^ 2 + θ 0 / θ 1 ^ 2) +
        ((θ 0 ^ 2)⁻¹ + ((θ 1 + σ) ^ 2)⁻¹) * k := by
  have hB : 0 < θ 1 + σ := by linarith
  refine (norm_toEuclideanCLM_le _ _ _ _).trans ?_
  have e1 : |-trigammaIncrement (θ 0) k| ≤ (θ 0 ^ 2)⁻¹ * k := by
    rw [abs_neg, abs_of_nonneg (trigammaIncrement_nonneg _ k)]
    exact trigammaIncrement_le ha k
  have e2 : |(θ 1)⁻¹ - (θ 1 + σ)⁻¹| ≤ (θ 1)⁻¹ + (θ 1 + σ)⁻¹ := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have e3 : |(θ 0 + k) / (θ 1 + σ) ^ 2 - θ 0 / θ 1 ^ 2| ≤
      θ 0 / (θ 1 + σ) ^ 2 + ((θ 1 + σ) ^ 2)⁻¹ * k + θ 0 / θ 1 ^ 2 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact le_of_eq (by ring)
  linarith

private lemma neg_inverse_neg_apply {S : E₂ →L[ℝ] E₂} (hS : IsUnit S) (y : E₂) :
    -Ring.inverse (-S) y = Ring.inverse S y := by
  have h := inverse_apply_apply hS.neg
    (Ring.inverse S y)
  rw [neg_apply,
    apply_inverse_apply hS, map_neg] at h
  rw [← h]

private lemma integrable_norm_countScore_sq {σ : ℝ} (hσ : 0 ≤ σ) {θ₀ : E₂} (ha : 0 < θ₀ 0)
    (hb : 0 < θ₀ 1) {μX : Measure ℕ} [IsFiniteMeasure μX]
    (hk2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) μX) :
    Integrable (fun k => ‖countScore σ θ₀ k‖ ^ 2) μX := by
  set A := |log (θ₀ 1)| + |log (θ₀ 1 + σ)| + θ₀ 0 / θ₀ 1 + θ₀ 0 / (θ₀ 1 + σ)
  set B := (θ₀ 0)⁻¹ + (θ₀ 1 + σ)⁻¹
  refine ((integrable_const (2 * A ^ 2)).add (hk2.const_mul (2 * B ^ 2))).mono'
    continuous_of_discreteTopology.aestronglyMeasurable (ae_of_all _ fun k => ?_)
  have h1 := norm_countScore_le hσ ha hb k
  have h2 : ‖countScore σ θ₀ k‖ ^ 2 ≤ (A + B * k) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [norm_pow, norm_norm]
  change ‖countScore σ θ₀ k‖ ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 * (k : ℝ) ^ 2
  nlinarith [sq_nonneg (A - B * k)]

/-- The rate component of the score equations at the truth forces the marginal mean: if
`E[countScore σ θ₀ K] = 0` then `E K = σ a / b`, since `a/b - (a + E K)/(b + σ) = 0`. -/
theorem integral_natCast_of_integral_countScore {σ : ℝ} (hσ : 0 ≤ σ) {θ₀ : E₂} (ha : 0 < θ₀ 0)
    (hb : 0 < θ₀ 1) {μX : Measure ℕ} [IsProbabilityMeasure μX]
    (hk : Integrable (fun k : ℕ => (k : ℝ)) μX) (hscore : ∫ k, countScore σ θ₀ k ∂μX = 0) :
    ∫ k, (k : ℝ) ∂μX = σ * θ₀ 0 / θ₀ 1 := by
  have hB : 0 < θ₀ 1 + σ := by linarith
  have hint : Integrable (countScore σ θ₀) μX :=
    integrable_nat_of_norm_le hk (norm_countScore_le hσ ha hb)
  have h1 := congrArg (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) hscore
  rw [← (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).integral_comp_comm hint, map_zero] at h1
  have hlin : Integrable (fun k : ℕ => (θ₀ 0 + k) / (θ₀ 1 + σ)) μX :=
    ((integrable_const _).add hk).div_const _
  have e : ∀ k, EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2) (countScore σ θ₀ k) =
      θ₀ 0 / θ₀ 1 - (θ₀ 0 + k) / (θ₀ 1 + σ) := fun k => rfl
  simp_rw [e] at h1
  rw [integral_sub (integrable_const _) hlin, integral_div (f := fun k : ℕ => θ₀ 0 + (k : ℝ)),
    integral_add (integrable_const _) hk] at h1
  simp only [integral_const, probReal_univ, one_smul] at h1
  field_simp at h1
  field_simp
  linarith

private lemma ball_coord_ge {θ₀ θ : E₂} (hθ : θ ∈ Metric.ball θ₀ (min (θ₀ 0) (θ₀ 1) / 2)) :
    min (θ₀ 0) (θ₀ 1) / 2 ≤ θ 0 ∧ min (θ₀ 0) (θ₀ 1) / 2 ≤ θ 1 := by
  rw [Metric.mem_ball, dist_eq_norm] at hθ
  have h0 : |θ 0 - θ₀ 0| ≤ ‖θ - θ₀‖ := by simpa using abs_apply_le_norm (θ - θ₀) 0
  have h1 : |θ 1 - θ₀ 1| ≤ ‖θ - θ₀‖ := by simpa using abs_apply_le_norm (θ - θ₀) 1
  have m0 := min_le_left (θ₀ 0) (θ₀ 1)
  have m1 := min_le_right (θ₀ 0) (θ₀ 1)
  have n0 := neg_abs_le (θ 0 - θ₀ 0)
  have n1 := neg_abs_le (θ 1 - θ₀ 1)
  constructor <;> linarith

/-- **Asymptotic normality of the joint count MLE.** Let `X₀, X₁, …` be i.i.d. counts with law
`μX` on `ℕ` with finite second moment, and let `θ₀ = (a, b)`, `a, b, σ > 0`. Assume the
**score equations at the truth** `E[countScore σ θ₀ K] = 0` (Fisher consistency of the shape and
rate equations of `HierarchicalCountMLE`; the rate equation forces the marginal mean
`E K = σ a / b`, `integral_natCast_of_integral_countScore`) and the profile-information condition
`τ = E[∑_{j<K} 1 / (a + j)²] > σ / (a (b + σ))`, which makes the Fisher information
`I = countFisherInfo a b σ τ` invertible. Let `θhat n` be a consistent sequence of roots of the
joint score equations `∑_{i<n} countScore σ θ (X i) = 0`, i.e. of
`shapeScore = rateScore = 0` (`sum_countScore`), with probability tending to one. Then
`√n (θhat n - θ₀) → I⁻¹ Y` in distribution, where `Y ~ N(0, E[ψ ψᵀ])`, `ψ = countScore σ θ₀ K`,
is given through its projections. Under the information identity `E[ψ ψᵀ] = I` this is
`N(0, I⁻¹)` (`tendstoInDistribution_countMLE_of_info`).

Source: Cramér (1946), §33.3; Lehmann & Casella (1998), Theorem 6.5.1; instantiated from
`VectorInference.tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation`. -/
theorem tendstoInDistribution_countMLE {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {σ : ℝ} (hσ : 0 < σ) {θ₀ : E₂} (ha : 0 < θ₀ 0) (hb : 0 < θ₀ 1)
    {μX : Measure ℕ} {X : ℕ → Ω → ℕ} (hX_law : ∀ i, HasLaw (X i) μX P)
    (hX_indep : iIndepFun X P) (hk2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) μX)
    (hscore : ∫ k, countScore σ θ₀ k ∂μX = 0)
    (hτ : σ / (θ₀ 0 * (θ₀ 1 + σ)) < ∫ k, trigammaIncrement (θ₀ 0) k ∂μX)
    {θhat : ℕ → Ω → E₂} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ range n, countScore σ (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Y : Ω' → E₂} (hY_meas : AEMeasurable Y P')
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫)
      (gaussianReal 0 (∫ k, ⟪countScore σ θ₀ k, t⟫ ^ 2 ∂μX).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n • (θhat n ω - θ₀)) atTop
      (fun ω => Ring.inverse
        (countFisherInfo (θ₀ 0) (θ₀ 1) σ (∫ k, trigammaIncrement (θ₀ 0) k ∂μX)) (Y ω))
      (fun _ => P) P' := by
  have : IsProbabilityMeasure μX := (hX_law 0).isProbabilityMeasure_iff.1 inferInstance
  have hk := integrable_natCast_of_sq hk2
  have hmean := integral_natCast_of_integral_countScore hσ.le ha hb hk hscore
  set c := min (θ₀ 0) (θ₀ 1) / 2 with hc_def
  have hc : 0 < c := by positivity
  have hc0 : c ≤ θ₀ 0 := by have := min_le_left (θ₀ 0) (θ₀ 1); linarith
  have hc1 : c ≤ θ₀ 1 := by have := min_le_right (θ₀ 0) (θ₀ 1); linarith
  have hderiv : ∀ k, ∀ θ ∈ Metric.ball θ₀ c,
      HasFDerivAt (fun t => countScore σ t k) (countHessian σ θ k) θ := fun k θ hθ =>
    hasFDerivAt_countScore hσ.le (hc.trans_le (ball_coord_ge hθ).1)
      (hc.trans_le (ball_coord_ge hθ).2) k
  have hfd0 : ∀ k, fderiv ℝ (fun t => countScore σ t k) θ₀ = countHessian σ θ₀ k := fun k =>
    (hderiv k θ₀ (Metric.mem_ball_self hc)).fderiv
  have hI := isUnit_countFisherInfo ha hb hσ hτ
  have hD : ∫ k, fderiv ℝ (fun t => countScore σ t k) θ₀ ∂μX =
      -countFisherInfo (θ₀ 0) (θ₀ 1) σ (∫ k, trigammaIncrement (θ₀ 0) k ∂μX) := by
    simp_rw [hfd0]
    exact integral_countHessian ha hb hσ.le hk hmean
  -- the Lipschitz envelope
  set M : ℕ → ℝ := fun k => 6 / c ^ 2 + 4 * (|θ₀ 0| + k) / c ^ 3 with hM_def
  have hM_int : Integrable M μX :=
    integrable_nat_of_norm_le hk (A := 6 / c ^ 2 + 4 * |θ₀ 0| / c ^ 3) (B := 4 / c ^ 3)
      fun k => by
        rw [norm_eq_abs, abs_of_nonneg (by positivity)]
        exact le_of_eq (by simp only [M]; ring)
  have hψ_sq := integrable_norm_countScore_sq hσ.le ha hb hk2
  have h := tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation
    hX_law hX_indep hc (fun k θ hθ => (hderiv k θ hθ).differentiableAt)
    (measurable_of_countable M) hM_int
    (fun k θ hθ => by
      rw [(hderiv k θ hθ).fderiv, hfd0]
      exact norm_countHessian_sub_le hσ.le hc (ball_coord_ge hθ).1 (ball_coord_ge hθ).2 hc0 hc1 k)
    (measurable_of_countable _) hψ_sq hscore
    (by simp_rw [hfd0]; exact continuous_of_discreteTopology.stronglyMeasurable)
    (by simp_rw [hfd0]; exact integrable_nat_of_norm_le hk (norm_countHessian_le hσ.le ha hb))
    (by rw [hD]; exact hI.neg) hθ_meas hroot hcons hY_meas hY
  rw [hD] at h
  exact h.congr (fun n => ae_of_all _ fun ω => rfl)
    (ae_of_all _ fun ω => neg_inverse_neg_apply hI (Y ω))

/-- **Asymptotic normality of the joint count MLE, information form.** Under the hypotheses of
`tendstoInDistribution_countMLE` and the information identity `E ⟪ψ, t⟫² = ⟪I t, t⟫`
(`ψ = countScore σ θ₀ K`, `I = countFisherInfo a b σ τ`), `√n (θhat n - θ₀) → I⁻¹ Y` with
`Y ~ N(0, I)`, so the limit is `N(0, I⁻¹)` (`hasLaw_inner_inverse_countFisherInfo`). -/
theorem tendstoInDistribution_countMLE_of_info {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {σ : ℝ} (hσ : 0 < σ) {θ₀ : E₂} (ha : 0 < θ₀ 0) (hb : 0 < θ₀ 1)
    {μX : Measure ℕ} {X : ℕ → Ω → ℕ} (hX_law : ∀ i, HasLaw (X i) μX P)
    (hX_indep : iIndepFun X P) (hk2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) μX)
    (hscore : ∫ k, countScore σ θ₀ k ∂μX = 0)
    (hτ : σ / (θ₀ 0 * (θ₀ 1 + σ)) < ∫ k, trigammaIncrement (θ₀ 0) k ∂μX)
    (hinfo : ∀ t, ∫ k, ⟪countScore σ θ₀ k, t⟫ ^ 2 ∂μX =
      ⟪countFisherInfo (θ₀ 0) (θ₀ 1) σ (∫ k, trigammaIncrement (θ₀ 0) k ∂μX) t, t⟫)
    {θhat : ℕ → Ω → E₂} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ range n, countScore σ (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Y : Ω' → E₂} (hY_meas : AEMeasurable Y P')
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫) (gaussianReal 0
      (⟪countFisherInfo (θ₀ 0) (θ₀ 1) σ (∫ k, trigammaIncrement (θ₀ 0) k ∂μX) t, t⟫).toNNReal)
      P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n • (θhat n ω - θ₀)) atTop
      (fun ω => Ring.inverse
        (countFisherInfo (θ₀ 0) (θ₀ 1) σ (∫ k, trigammaIncrement (θ₀ 0) k ∂μX)) (Y ω))
      (fun _ => P) P' :=
  tendstoInDistribution_countMLE hσ ha hb hX_law hX_indep hk2 hscore hτ hθ_meas hroot hcons
    hY_meas fun t => by rw [hinfo]; exact hY t

/-! ### The method-of-moments estimator as a Z-estimator -/

/-- The moment estimating function of one count `k` at `θ = (a, b)`:
`(b k - σ a, b² k² - σ a b - σ² a - σ² a²)`, which is `(b (k - μ), b² (k² - μ - μ² / a - μ²))`
with `μ = σ a / b`. Its sample equations `∑ᵢ momEstFun σ θ kᵢ = 0` say that the sample mean and
second moment match the negative binomial ones, so for overdispersed samples their unique
positive root is the moment estimate (`sum_momEstFun_mom_eq_zero`). -/
noncomputable def momEstFun (σ : ℝ) (θ : E₂) (k : ℕ) : E₂ :=
  !₂[θ 1 * k - σ * θ 0, θ 1 ^ 2 * k ^ 2 - σ * θ 0 * θ 1 - σ ^ 2 * θ 0 - σ ^ 2 * θ 0 ^ 2]

/-- The derivative of `momEstFun σ · k` at `θ = (a, b)`:
`[[-σ, k], [-σ b - σ² - 2 σ² a, 2 b k² - σ a]]`. -/
noncomputable def momEstDeriv (σ : ℝ) (θ : E₂) (k : ℕ) : E₂ →L[ℝ] E₂ :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) !![-σ, (k : ℝ); -(σ * θ 1) - σ ^ 2 - 2 * σ ^ 2 * θ 0,
    2 * θ 1 * k ^ 2 - σ * θ 0]

/-- The expected derivative of the moment estimating function at `(a, b)` under the negative
binomial mean and second moment: `[[-σ, σ a / b], [-σ b - σ² - 2 σ² a, σ a + 2 σ² a (1 + a) / b]]`
(`integral_momEstDeriv`). Its determinant is `-σ³ a / b`. -/
noncomputable def momJacobian (a b σ : ℝ) : E₂ →L[ℝ] E₂ :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) !![-σ, σ * a / b; -(σ * b) - σ ^ 2 - 2 * σ ^ 2 * a,
    σ * a + 2 * σ ^ 2 * a * (1 + a) / b]

/-- The moment estimating function is differentiable in `θ` with derivative `momEstDeriv`. -/
theorem hasFDerivAt_momEstFun (σ : ℝ) (θ : E₂) (k : ℕ) :
    HasFDerivAt (fun t => momEstFun σ t k) (momEstDeriv σ θ k) θ := by
  have hp0 : HasFDerivAt (fun t : E₂ => t 0) (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) θ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt
  have hp1 : HasFDerivAt (fun t : E₂ => t 1) (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) θ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
  have hf := (hp1.mul_const (k : ℝ)).sub (hp0.const_mul σ)
  have hg := (((((hp1.mul hp1).mul_const ((k : ℝ) ^ 2)).sub ((hp0.const_mul σ).mul hp1)).sub
    (hp0.const_mul (σ ^ 2))).sub ((hp0.mul hp0).const_mul (σ ^ 2)))
  convert hasFDerivAt_toLp_two hf hg using 1
  · funext t
    ext i
    fin_cases i
    · simp [momEstFun]
    · simp [momEstFun]
      ring
  · ext v i
    fin_cases i
    · simp [momEstDeriv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    · simp [momEstDeriv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring

/-- **Lipschitz envelope of the moment derivative**, valid globally:
`‖momEstDeriv σ θ k - momEstDeriv σ θ₀ k‖ ≤ (2 |σ| + 2 σ² + 2 k²) ‖θ - θ₀‖`. -/
theorem norm_momEstDeriv_sub_le (σ : ℝ) (θ₀ θ : E₂) (k : ℕ) :
    ‖momEstDeriv σ θ k - momEstDeriv σ θ₀ k‖ ≤ (2 * |σ| + 2 * σ ^ 2 + 2 * k ^ 2) * ‖θ - θ₀‖ := by
  set r := ‖θ - θ₀‖
  have hra : |θ 0 - θ₀ 0| ≤ r := by simpa using abs_apply_le_norm (θ - θ₀) 0
  have hrb : |θ 1 - θ₀ 1| ≤ r := by simpa using abs_apply_le_norm (θ - θ₀) 1
  have hsub : momEstDeriv σ θ k - momEstDeriv σ θ₀ k = Matrix.toEuclideanCLM (𝕜 := ℝ)
      !![0, 0; -σ * (θ 1 - θ₀ 1) - 2 * σ ^ 2 * (θ 0 - θ₀ 0),
        2 * (k : ℝ) ^ 2 * (θ 1 - θ₀ 1) - σ * (θ 0 - θ₀ 0)] := by
    rw [momEstDeriv, momEstDeriv, ← map_sub]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  rw [hsub]
  refine (norm_toEuclideanCLM_le _ _ _ _).trans ?_
  have e1 : |-σ * (θ 1 - θ₀ 1) - 2 * σ ^ 2 * (θ 0 - θ₀ 0)| ≤ (|σ| + 2 * σ ^ 2) * r := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * σ ^ 2)]
    nlinarith [abs_nonneg σ, sq_nonneg σ]
  have e2 : |2 * (k : ℝ) ^ 2 * (θ 1 - θ₀ 1) - σ * (θ 0 - θ₀ 0)| ≤ (2 * k ^ 2 + |σ|) * r := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_nonneg (sq_nonneg (k : ℝ))]
    nlinarith [abs_nonneg σ, sq_nonneg (k : ℝ)]
  simp only [abs_zero, zero_add]
  nlinarith

/-- **The Jacobian of the moment equations.** If the count law has the negative binomial mean
`m = σ a / b` and second moment `m + m² / a + m²`, the expected derivative of the moment
estimating function at `(a, b)` is `momJacobian a b σ`. -/
theorem integral_momEstDeriv {σ a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {μX : Measure ℕ} [IsProbabilityMeasure μX] (hk2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) μX)
    (hmean : ∫ k, (k : ℝ) ∂μX = σ * a / b)
    (hsq : ∫ k, (k : ℝ) ^ 2 ∂μX = σ * a / b + (σ * a / b) ^ 2 / a + (σ * a / b) ^ 2) :
    ∫ k, momEstDeriv σ !₂[a, b] k ∂μX = momJacobian a b σ := by
  have hk := integrable_natCast_of_sq hk2
  have h4 : Integrable (fun k : ℕ => 2 * b * (k : ℝ) ^ 2 - σ * a) μX :=
    (hk2.const_mul _).sub (integrable_const _)
  unfold momEstDeriv
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [integral_toEuclideanCLM (integrable_const _) hk (integrable_const _) h4, momJacobian]
  congr 1
  have e4 : ∫ k, (2 * b * (k : ℝ) ^ 2 - σ * a) ∂μX = σ * a + 2 * σ ^ 2 * a * (1 + a) / b := by
    rw [integral_sub (hk2.const_mul _) (integrable_const _), integral_const_mul, hsq]
    simp only [integral_const, probReal_univ, one_smul]
    field_simp
    ring
  rw [e4, hmean]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The Jacobian of the moment equations is invertible for `a, b, σ > 0`. -/
theorem isUnit_momJacobian {a b σ : ℝ} (ha : 0 < a) (hb : 0 < b) (hσ : 0 < σ) :
    IsUnit (momJacobian a b σ) := by
  rw [momJacobian]
  refine (Matrix.isUnit_iff_isUnit_det _ |>.2 ?_).map _
  rw [Matrix.det_fin_two_of]
  refine Ne.isUnit ?_
  have : -σ * (σ * a + 2 * σ ^ 2 * a * (1 + a) / b) -
      σ * a / b * (-(σ * b) - σ ^ 2 - 2 * σ ^ 2 * a) = -(σ ^ 3 * a / b) := by
    field_simp
    ring
  rw [this, neg_ne_zero]
  positivity

/-- **The moment estimate solves the moment estimating equations.** If `n > 0` counts have
sample mean `M` and biased sample variance `V` with `0 < M < V`, then
`∑_{i<n} momEstFun σ (momShape M V, momRate σ M V) kᵢ = 0`. -/
theorem sum_momEstFun_mom_eq_zero (σ : ℝ) {n : ℕ} (k : ℕ → ℕ)
    (hM : 0 < (n : ℝ)⁻¹ * ∑ i ∈ range n, (k i : ℝ))
    (hMV : (n : ℝ)⁻¹ * ∑ i ∈ range n, (k i : ℝ) <
      (n : ℝ)⁻¹ * ∑ i ∈ range n, (k i : ℝ) ^ 2 - ((n : ℝ)⁻¹ * ∑ i ∈ range n, (k i : ℝ)) ^ 2) :
    ∑ i ∈ range n, momEstFun σ !₂[momShape ((n : ℝ)⁻¹ * ∑ i ∈ range n, (k i : ℝ))
      ((n : ℝ)⁻¹ * ∑ i ∈ range n, (k i : ℝ) ^ 2 - ((n : ℝ)⁻¹ * ∑ i ∈ range n, (k i : ℝ)) ^ 2),
      momRate σ ((n : ℝ)⁻¹ * ∑ i ∈ range n, (k i : ℝ))
      ((n : ℝ)⁻¹ * ∑ i ∈ range n, (k i : ℝ) ^ 2 -
        ((n : ℝ)⁻¹ * ∑ i ∈ range n, (k i : ℝ)) ^ 2)] (k i) = 0 := by
  have hn : (n : ℝ) ≠ 0 := by
    rintro h
    rw [h, inv_zero, zero_mul] at hM
    exact lt_irrefl _ hM
  set M := (n : ℝ)⁻¹ * ∑ i ∈ range n, (k i : ℝ)
  set V := (n : ℝ)⁻¹ * ∑ i ∈ range n, (k i : ℝ) ^ 2 - M ^ 2
  have hS₁ : ∑ i ∈ range n, (k i : ℝ) = n * M := by simp only [M]; field_simp
  have hS₂ : ∑ i ∈ range n, (k i : ℝ) ^ 2 = n * (V + M ^ 2) := by
    simp only [V, M]; field_simp; ring
  have hD : 0 < V - M := by linarith
  ext j
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, WithLp.ofLp_sum, Finset.sum_apply, momEstFun,
      Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply]
    rw [sum_sub_distrib, ← sum_mul, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
    simp only [momShape, momRate]
    rw [hS₁]
    field_simp
    ring
  · simp only [Fin.mk_one, Fin.isValue, WithLp.ofLp_sum, Finset.sum_apply, momEstFun,
      Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply]
    rw [sum_sub_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum, sum_const, sum_const,
      sum_const, card_range, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
    simp only [momShape, momRate]
    rw [hS₂]
    field_simp
    ring

private lemma toLp_two_eq (x y : ℝ) :
    !₂[x, y] = x • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
      y • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
  ext i
  fin_cases i <;> simp

private lemma continuous_toLp_two : Continuous fun p : ℝ × ℝ => !₂[p.1, p.2] := by
  simp_rw [toLp_two_eq]
  fun_prop

private lemma integral_toLp_two {μX : Measure ℕ} {f g : ℕ → ℝ} (hf : Integrable f μX)
    (hg : Integrable g μX) : ∫ k, !₂[f k, g k] ∂μX = !₂[∫ k, f k ∂μX, ∫ k, g k ∂μX] := by
  simp_rw [toLp_two_eq]
  rw [integral_add (hf.smul_const _) (hg.smul_const _), integral_smul_const, integral_smul_const]

/-- The moment equations hold at the truth: if the count law has the negative binomial mean and
second moment at `(a, b)`, then `E[momEstFun σ (a, b) K] = 0`. -/
theorem integral_momEstFun {σ a b : ℝ} (hb : 0 < b)
    {μX : Measure ℕ} [IsProbabilityMeasure μX] (hk2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) μX)
    (hmean : ∫ k, (k : ℝ) ∂μX = σ * a / b)
    (hsq : ∫ k, (k : ℝ) ^ 2 ∂μX = σ * a / b + (σ * a / b) ^ 2 / a + (σ * a / b) ^ 2) :
    ∫ k, momEstFun σ !₂[a, b] k ∂μX = 0 := by
  have hk := integrable_natCast_of_sq hk2
  have j0 : Integrable (fun k : ℕ => b * (k : ℝ) - σ * a) μX :=
    (hk.const_mul b).sub (integrable_const _)
  have j1 : Integrable (fun k : ℕ => b ^ 2 * (k : ℝ) ^ 2 - σ * a * b) μX :=
    (hk2.const_mul _).sub (integrable_const _)
  have j2 : Integrable (fun k : ℕ => b ^ 2 * (k : ℝ) ^ 2 - σ * a * b - σ ^ 2 * a) μX :=
    j1.sub (integrable_const _)
  have j3 : Integrable
      (fun k : ℕ => b ^ 2 * (k : ℝ) ^ 2 - σ * a * b - σ ^ 2 * a - σ ^ 2 * a ^ 2) μX :=
    j2.sub (integrable_const _)
  have i0 : ∫ k, (b * (k : ℝ) - σ * a) ∂μX = 0 := by
    rw [integral_sub (hk.const_mul b) (integrable_const _), integral_const_mul, hmean]
    simp only [integral_const, probReal_univ, one_smul]
    field_simp
    ring
  have i1 : ∫ k, (b ^ 2 * (k : ℝ) ^ 2 - σ * a * b - σ ^ 2 * a - σ ^ 2 * a ^ 2) ∂μX = 0 := by
    rw [integral_sub j2 (integrable_const _), integral_sub j1 (integrable_const _),
      integral_sub (hk2.const_mul _) (integrable_const _), integral_const_mul, hsq]
    simp only [integral_const, probReal_univ, one_smul]
    field_simp
    ring
  unfold momEstFun
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [integral_toLp_two j0 j3, i0, i1]
  ext i
  fin_cases i <;> simp

/-- The method-of-moments estimate `(momShape M̂ₙ V̂ₙ, momRate σ M̂ₙ V̂ₙ)` of the hyperparameter
`(a, b)` from the first `n` counts, with the sample mean `M̂ₙ` and biased sample variance `V̂ₙ` of
`HierarchicalCount`. -/
noncomputable def momEstimator {Ω : Type*} (σ : ℝ) (X : ℕ → Ω → ℕ) (n : ℕ) (ω : Ω) : E₂ :=
  !₂[momShape (sampleMean (fun i ω => (X i ω : ℝ)) n ω) (sampleVar (fun i ω => (X i ω : ℝ)) n ω),
    momRate σ (sampleMean (fun i ω => (X i ω : ℝ)) n ω) (sampleVar (fun i ω => (X i ω : ℝ)) n ω)]

private lemma natCast_sq_le_pow_four (k : ℕ) : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := by
  have h := natCast_le_sq k
  have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_le_mul_of_nonneg_left h h0, mul_le_mul_of_nonneg_left h (sq_nonneg (k : ℝ))]

private lemma integrable_norm_momEstFun_sq (σ : ℝ) {a b : ℝ} (hb : 0 < b) {μX : Measure ℕ}
    [IsFiniteMeasure μX] (hk4 : Integrable (fun k : ℕ => (k : ℝ) ^ 4) μX) :
    Integrable (fun k => ‖momEstFun σ !₂[a, b] k‖ ^ 2) μX := by
  set G := |σ * a| + |σ * a * b + σ ^ 2 * a + σ ^ 2 * a ^ 2|
  set H := b + b ^ 2
  have hg_bound : ∀ k : ℕ, ‖momEstFun σ !₂[a, b] k‖ ≤ G + H * (k : ℝ) ^ 2 := by
    intro k
    refine (norm_le_abs_add_abs _).trans ?_
    simp only [momEstFun, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have e1 : |b * (k : ℝ) - σ * a| ≤ b * k + |σ * a| := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (by positivity)]
    have e2 : |b ^ 2 * (k : ℝ) ^ 2 - σ * a * b - σ ^ 2 * a - σ ^ 2 * a ^ 2| ≤
        b ^ 2 * k ^ 2 + |σ * a * b + σ ^ 2 * a + σ ^ 2 * a ^ 2| := by
      have : b ^ 2 * (k : ℝ) ^ 2 - σ * a * b - σ ^ 2 * a - σ ^ 2 * a ^ 2 =
          b ^ 2 * k ^ 2 - (σ * a * b + σ ^ 2 * a + σ ^ 2 * a ^ 2) := by ring
      rw [this]
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (by positivity)]
    have e3 := mul_le_mul_of_nonneg_left (natCast_le_sq k) hb.le
    simp only [G, H]
    nlinarith
  refine ((integrable_const (2 * G ^ 2)).add (hk4.const_mul (2 * H ^ 2))).mono'
    continuous_of_discreteTopology.aestronglyMeasurable (ae_of_all _ fun k => ?_)
  have h2 : ‖momEstFun σ !₂[a, b] k‖ ^ 2 ≤ (G + H * (k : ℝ) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hg_bound k) 2
  rw [norm_pow, norm_norm]
  change ‖momEstFun σ !₂[a, b] k‖ ^ 2 ≤ 2 * G ^ 2 + 2 * H ^ 2 * (k : ℝ) ^ 4
  nlinarith [sq_nonneg (G - H * (k : ℝ) ^ 2)]

/-- **Asymptotic normality of the method-of-moments estimator.** Let `X₀, X₁, …` be i.i.d. counts
with law `μX` on `ℕ`, with finite fourth moment and with the negative binomial mean
`m = σ a / b` and second moment `m + m² / a + m²` at the true hyperparameter `(a, b)`,
`a, b, σ > 0`. Then the moment estimates `θhat n = momEstimator σ X n` satisfy
`√n (θhat n - (a, b)) → -J⁻¹ Y` in distribution, with `J = momJacobian a b σ` and
`Y ~ N(0, E[g gᵀ])`, `g = momEstFun σ (a, b) K`, given through its projections. Unlike
`tendstoInDistribution_countMLE`, no root or consistency hypothesis is needed: the moment estimate
solves the moment equations once the sample is overdispersed (`sum_momEstFun_mom_eq_zero`), which
happens with probability tending to one, and it is strongly consistent by the strong law.

Source: the delta method for moment estimators (van der Vaart 1998, §4.1 and Theorem 5.41);
instantiated from `VectorInference.tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation`. -/
theorem tendstoInDistribution_mom {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hb : 0 < b)
    {μX : Measure ℕ} {X : ℕ → Ω → ℕ} (hX_law : ∀ i, HasLaw (X i) μX P)
    (hX_indep : iIndepFun X P) (hk4 : Integrable (fun k : ℕ => (k : ℝ) ^ 4) μX)
    (hmean : ∫ k, (k : ℝ) ∂μX = σ * a / b)
    (hsq : ∫ k, (k : ℝ) ^ 2 ∂μX = σ * a / b + (σ * a / b) ^ 2 / a + (σ * a / b) ^ 2)
    {Y : Ω' → E₂} (hY_meas : AEMeasurable Y P')
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫)
      (gaussianReal 0 (∫ k, ⟪momEstFun σ !₂[a, b] k, t⟫ ^ 2 ∂μX).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n • (momEstimator σ X n ω - !₂[a, b])) atTop
      (fun ω => -Ring.inverse (momJacobian a b σ) (Y ω)) (fun _ => P) P' := by
  have : IsProbabilityMeasure μX := (hX_law 0).isProbabilityMeasure_iff.1 inferInstance
  have hk2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) μX :=
    hk4.mono' continuous_of_discreteTopology.aestronglyMeasurable
      (ae_of_all _ fun k => by
        rw [norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact natCast_sq_le_pow_four k)
  have hk := integrable_natCast_of_sq hk2
  set m := σ * a / b with hm_def
  set q := m + m ^ 2 / a + m ^ 2 with hq_def
  have hm0 : 0 < m := by positivity
  have hMV : m < q - m ^ 2 := by
    have : 0 < m ^ 2 / a := by positivity
    simp only [q]; linarith
  -- the real-valued counts, their squares, and the strong law
  set Xr : ℕ → Ω → ℝ := fun i ω => (X i ω : ℝ) with hXr_def
  have hcast : Measurable fun k : ℕ => (k : ℝ) := measurable_of_countable _
  have hsq_meas : Measurable fun x : ℝ => x ^ 2 := measurable_id.pow_const 2
  have hXr_m : ∀ i, AEMeasurable (Xr i) P := fun i =>
    hcast.comp_aemeasurable (hX_law i).aemeasurable
  have hindep : Pairwise ((· ⟂ᵢ[P] ·) on Xr) := fun i j hij =>
    (hX_indep.indepFun hij).comp hcast hcast
  have hident : ∀ i, IdentDistrib (Xr i) (Xr 0) P P := fun i =>
    (⟨(hX_law i).aemeasurable, (hX_law 0).aemeasurable,
      by rw [(hX_law i).map_eq, (hX_law 0).map_eq]⟩ : IdentDistrib (X i) (X 0) P P).comp hcast
  have hint1 : Integrable (Xr 0) P := (hX_law 0).integrable_comp hk
  have hint2 : Integrable (fun ω => Xr 0 ω ^ 2) P := (hX_law 0).integrable_comp hk2
  have hE1 : P[Xr 0] = m :=
    ((hX_law 0).integral_comp (f := fun k : ℕ => (k : ℝ)) hcast.aestronglyMeasurable).trans hmean
  have hE2 : P[fun ω => Xr 0 ω ^ 2] = q :=
    ((hX_law 0).integral_comp (f := fun k : ℕ => (k : ℝ) ^ 2)
      (hsq_meas.comp hcast).aestronglyMeasurable).trans hsq
  have hSLLN1 := strong_law_ae Xr hint1 hindep hident
  have hSLLN2 := strong_law_ae (fun i ω => Xr i ω ^ 2) hint2
    (fun i j hij => (hindep hij).comp hsq_meas hsq_meas) (fun i => (hident i).comp hsq_meas)
  rw [hE1] at hSLLN1
  rw [hE2] at hSLLN2
  set Mn : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ range n, Xr i ω with hMn_def
  set Qn : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ range n, Xr i ω ^ 2 with hQn_def
  have hMn_m : ∀ n, AEMeasurable (Mn n) P := fun n =>
    (Finset.aemeasurable_fun_sum _ fun i _ => hXr_m i).const_mul _
  have hQn_m : ∀ n, AEMeasurable (Qn n) P := fun n =>
    (Finset.aemeasurable_fun_sum _ fun i _ => (hXr_m i).pow_const 2).const_mul _
  have hMn_ae : ∀ᵐ ω ∂P, Tendsto (fun n => Mn n ω) atTop (𝓝 m) := by
    filter_upwards [hSLLN1] with ω hω
    simpa only [smul_eq_mul] using hω
  have hQn_ae : ∀ᵐ ω ∂P, Tendsto (fun n => Qn n ω) atTop (𝓝 q) := by
    filter_upwards [hSLLN2] with ω hω
    simpa only [smul_eq_mul] using hω
  -- the estimator in terms of `Mn`, `Qn`
  have hest : ∀ n ω, momEstimator σ X n ω =
      !₂[momShape (Mn n ω) (Qn n ω - Mn n ω ^ 2), momRate σ (Mn n ω) (Qn n ω - Mn n ω ^ 2)] :=
    fun n ω => rfl
  have hθ_meas : ∀ n, AEMeasurable (momEstimator σ X n) P := fun n => by
    have h1 : AEMeasurable (fun ω => momShape (Mn n ω) (Qn n ω - Mn n ω ^ 2)) P :=
      ((hMn_m n).pow_const 2).div (((hQn_m n).sub ((hMn_m n).pow_const 2)).sub (hMn_m n))
    have h2 : AEMeasurable (fun ω => momRate σ (Mn n ω) (Qn n ω - Mn n ω ^ 2)) P :=
      ((hMn_m n).const_mul σ).div (((hQn_m n).sub ((hMn_m n).pow_const 2)).sub (hMn_m n))
    exact continuous_toLp_two.measurable.comp_aemeasurable (h1.prodMk h2)
  -- the limits of the moment estimates
  obtain ⟨ha', hb'⟩ := eq_mom_of_moment_equations ha hb hσ hm_def.symm
    (show m + m ^ 2 / a = q - m ^ 2 by simp only [q]; ring)
  have hcons : TendstoInMeasure P (momEstimator σ X) atTop (fun _ => !₂[a, b]) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => (hθ_meas n).aestronglyMeasurable) ?_
    filter_upwards [hMn_ae, hQn_ae] with ω h1 h2
    obtain ⟨hA, hB, -⟩ := tendsto_mom_of_tendsto hσ hm0 hMV h1 h2
    rw [← ha'] at hA
    rw [← hb'] at hB
    exact (continuous_toLp_two.tendsto (a, b)).comp (hA.prodMk_nhds hB)
  -- roots of the moment equations with probability tending to one
  have hU : IsOpen {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 - p.1 ^ 2} :=
    (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_fst (continuous_snd.sub (continuous_fst.pow 2)))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU (m, q) ⟨hm0, hMV⟩
  have hMn_meas : TendstoInMeasure P Mn atTop (fun _ => m) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hMn_m n).aestronglyMeasurable) hMn_ae
  have hQn_meas : TendstoInMeasure P Qn atTop (fun _ => q) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hQn_m n).aestronglyMeasurable) hQn_ae
  have hsub : ∀ n, {ω | ∑ i ∈ range n, momEstFun σ (momEstimator σ X n ω) (X i ω) ≠ 0} ⊆
      {ω | ENNReal.ofReal ε ≤ edist (Mn n ω) m} ∪ {ω | ENNReal.ofReal ε ≤ edist (Qn n ω) q} := by
    intro n ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, edist_lt_ofReal] at hcon
    have hmem : (Mn n ω, Qn n ω) ∈ Metric.ball (m, q) ε := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt hcon.1 hcon.2
    obtain ⟨h1, h2⟩ := hball hmem
    exact hω (sum_momEstFun_mom_eq_zero σ (fun i => X i ω) h1 h2)
  have hroot : Tendsto (fun n => P {ω | ∑ i ∈ range n,
      momEstFun σ (momEstimator σ X n ω) (X i ω) ≠ 0}) atTop (𝓝 0) := by
    have hlim := (hMn_meas _ (ENNReal.ofReal_pos.2 hε)).add (hQn_meas _ (ENNReal.ofReal_pos.2 hε))
    rw [add_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => zero_le) (fun n => (measure_mono (hsub n)).trans (measure_union_le _ _))
  -- the Z-estimator theorem
  have hfd : ∀ k θ, fderiv ℝ (fun t => momEstFun σ t k) θ = momEstDeriv σ θ k := fun k θ =>
    (hasFDerivAt_momEstFun σ θ k).fderiv
  have hJ := isUnit_momJacobian ha hb hσ
  have hD : ∫ k, fderiv ℝ (fun t => momEstFun σ t k) !₂[a, b] ∂μX = momJacobian a b σ := by
    simp_rw [hfd]
    exact integral_momEstDeriv ha hb hk2 hmean hsq
  have hψ_sq := integrable_norm_momEstFun_sq σ (a := a) hb hk4
  have hDg_int : Integrable (fun k => momEstDeriv σ !₂[a, b] k) μX := by
    refine ((integrable_const (|σ| + |σ * b + σ ^ 2 + 2 * σ ^ 2 * a| + |σ * a|)).add
      (hk2.const_mul (1 + 2 * b))).mono'
      continuous_of_discreteTopology.aestronglyMeasurable (ae_of_all _ fun k => ?_)
    refine (norm_toEuclideanCLM_le _ _ _ _).trans ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have e1 : |-(σ * b) - σ ^ 2 - 2 * σ ^ 2 * a| = |σ * b + σ ^ 2 + 2 * σ ^ 2 * a| := by
      rw [← abs_neg]; ring_nf
    have e2 : |2 * b * (k : ℝ) ^ 2 - σ * a| ≤ 2 * b * k ^ 2 + |σ * a| := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (by positivity)]
    have e3 := natCast_le_sq k
    rw [abs_neg, Nat.abs_cast, e1]
    change _ ≤ |σ| + |σ * b + σ ^ 2 + 2 * σ ^ 2 * a| + |σ * a| + (1 + 2 * b) * (k : ℝ) ^ 2
    nlinarith
  have hMg_int : Integrable (fun k : ℕ => 2 * |σ| + 2 * σ ^ 2 + 2 * (k : ℝ) ^ 2) μX :=
    (integrable_const _).add (hk2.const_mul 2)
  have h := tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation
    hX_law hX_indep one_pos (fun k θ _ => (hasFDerivAt_momEstFun σ θ k).differentiableAt)
    (M := fun k : ℕ => 2 * |σ| + 2 * σ ^ 2 + 2 * (k : ℝ) ^ 2) (measurable_of_countable _)
    hMg_int
    (fun k θ _ => by rw [hfd, hfd]; exact norm_momEstDeriv_sub_le σ _ θ k)
    (measurable_of_countable _) hψ_sq (integral_momEstFun hb hk2 hmean hsq)
    (by simp_rw [hfd]; exact continuous_of_discreteTopology.stronglyMeasurable)
    (by simp_rw [hfd]; exact hDg_int)
    (by rw [hD]; exact hJ) hθ_meas hroot hcons hY_meas hY
  rw [hD] at h
  exact h

/-! ### Efficiency of the MLE relative to the moment estimator -/

/-- **Efficiency of the count MLE relative to the moment estimator.** Let the count law `μX`
have finite fourth moment, let `θ₀ = (a, b)` with `a, b, σ > 0` satisfy the profile-information
condition `σ / (a (b + σ)) < τ`, `τ = E[∑_{j<K} 1/(a + j)²]`, and assume the two regularity
identities of the model at `θ₀`:

* the **information identity** `⟪I z, z⟫ = E ⟪ψ, z⟫²`, `I = countFisherInfo a b σ τ`,
  `ψ = countScore σ θ₀ K` (second Bartlett identity);
* **differentiated unbiasedness of the moment equations**
  `⟪J x, w⟫ = -E[⟪ψ, x⟫ ⟪g, w⟫]`, `J = momJacobian a b σ`, `g = momEstFun σ θ₀ K`, which is
  `∂_θ E_θ[g(θ, K)] = 0` differentiated under the expectation.

Then for every direction `u`, `⟪I⁻¹ u, u⟫ ≤ E ⟪g, (J⁻¹)ᵀ u⟫²`. The left side is the variance of
`⟪Z, u⟫` for the limit `Z ~ N(0, I⁻¹)` of the MLE and the right side that of the limit
`-J⁻¹ N(0, E[g gᵀ])` of the moment estimator (`variance_inner_countMLE_limit_le`): the
asymptotic covariance of the moment estimator dominates the inverse Fisher information in the
Loewner order.

Source: Godambe (1960); the efficiency of the negative binomial moment estimator was studied by
Fisher (1941) and Anscombe (1950). -/
theorem inner_inverse_countFisherInfo_le {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hb : 0 < b)
    {μX : Measure ℕ} [IsProbabilityMeasure μX] (hk4 : Integrable (fun k : ℕ => (k : ℝ) ^ 4) μX)
    (hτ : σ / (a * (b + σ)) < ∫ k, trigammaIncrement a k ∂μX)
    (hinfo : ∀ z, ⟪countFisherInfo a b σ (∫ k, trigammaIncrement a k ∂μX) z, z⟫ =
      ∫ k, ⟪countScore σ !₂[a, b] k, z⟫ ^ 2 ∂μX)
    (hunb : ∀ x w, ⟪momJacobian a b σ x, w⟫ =
      -∫ k, ⟪countScore σ !₂[a, b] k, x⟫ * ⟪momEstFun σ !₂[a, b] k, w⟫ ∂μX)
    (u : E₂) :
    ⟪Ring.inverse (countFisherInfo a b σ (∫ k, trigammaIncrement a k ∂μX)) u, u⟫ ≤
      ∫ k, ⟪momEstFun σ !₂[a, b] k,
        ContinuousLinearMap.adjoint (Ring.inverse (momJacobian a b σ)) u⟫ ^ 2 ∂μX := by
  have hk2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) μX :=
    hk4.mono' continuous_of_discreteTopology.aestronglyMeasurable
      (ae_of_all _ fun k => by
        rw [norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact natCast_sq_le_pow_four k)
  have ha' : (0 : ℝ) < (!₂[a, b] : E₂) 0 := ha
  have hb' : (0 : ℝ) < (!₂[a, b] : E₂) 1 := hb
  have hs_sq := integrable_norm_countScore_sq hσ.le ha' hb' hk2
  have hg_sq := integrable_norm_momEstFun_sq σ (a := a) hb hk4
  have hs_meas : AEStronglyMeasurable (countScore σ !₂[a, b]) μX :=
    continuous_of_discreteTopology.aestronglyMeasurable
  have hg_meas : AEStronglyMeasurable (momEstFun σ !₂[a, b]) μX :=
    continuous_of_discreteTopology.aestronglyMeasurable
  have hI := isUnit_countFisherInfo ha hb hσ hτ
  have hJ := isUnit_momJacobian ha hb hσ
  set w := ContinuousLinearMap.adjoint (Ring.inverse (momJacobian a b σ)) u with hw
  have hv : ∫ k, ⟪momEstFun σ !₂[a, b] k, w⟫ • countScore σ !₂[a, b] k ∂μX = -u := by
    refine ext_inner_right ℝ fun x => ?_
    rw [real_inner_comm, ← integral_inner (integrable_inner_smul hs_meas hs_sq hg_meas hg_sq w) x]
    have e1 : ∫ k, ⟪x, ⟪momEstFun σ !₂[a, b] k, w⟫ • countScore σ !₂[a, b] k⟫ ∂μX =
        -⟪momJacobian a b σ x, w⟫ := by
      rw [hunb, neg_neg]
      refine integral_congr_ae (ae_of_all _ fun k => ?_)
      simp only
      rw [real_inner_smul_right, real_inner_comm (countScore σ !₂[a, b] k) x, mul_comm]
    rw [e1, hw, ContinuousLinearMap.adjoint_inner_right,
      inverse_apply_apply hJ, inner_neg_left,
      real_inner_comm]
  have h := inner_inverse_le_integral_inner_sq hs_meas hs_sq hg_meas hg_sq hI hinfo w
  rwa [hv, map_neg, inner_neg_neg] at h

/-- **Law of the MLE limit.** If `⟪Y, t⟫ ~ N(0, ⟪I t, t⟫)` for every `t`, with `I` the
invertible Fisher information, then `⟪I⁻¹ Y, u⟫ ~ N(0, ⟪I⁻¹ u, u⟫)`. -/
theorem hasLaw_inner_inverse_countFisherInfo {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {a b σ τ : ℝ} (ha : 0 < a) (hb : 0 < b) (hσ : 0 < σ) (hτ : σ / (a * (b + σ)) < τ)
    {Y : Ω' → E₂}
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫) (gaussianReal 0 (⟪countFisherInfo a b σ τ t, t⟫).toNNReal)
      P') (u : E₂) :
    HasLaw (fun ω => ⟪Ring.inverse (countFisherInfo a b σ τ) (Y ω), u⟫)
      (gaussianReal 0 (⟪Ring.inverse (countFisherInfo a b σ τ) u, u⟫).toNNReal) P' := by
  have hI := isUnit_countFisherInfo ha hb hσ hτ
  have h := hY (Ring.inverse (countFisherInfo a b σ τ) u)
  rw [apply_inverse_apply hI,
    real_inner_comm] at h
  convert h using 2 with ω
  exact inner_inverse_comm
    (inner_countFisherInfo_comm a b σ τ) hI _ _

/-- **Law of the moment-estimator limit.** If `⟪Y, t⟫ ~ N(0, E ⟪g, t⟫²)` for every `t`,
`g = momEstFun σ (a, b) K`, then `⟪-J⁻¹ Y, u⟫ ~ N(0, E ⟪g, (J⁻¹)ᵀ u⟫²)`,
`J = momJacobian a b σ`. -/
theorem hasLaw_inner_neg_inverse_momJacobian {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} {σ a b : ℝ} {μX : Measure ℕ} {Y : Ω' → E₂}
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫)
      (gaussianReal 0 (∫ k, ⟪momEstFun σ !₂[a, b] k, t⟫ ^ 2 ∂μX).toNNReal) P') (u : E₂) :
    HasLaw (fun ω => ⟪-Ring.inverse (momJacobian a b σ) (Y ω), u⟫)
      (gaussianReal 0 (∫ k, ⟪momEstFun σ !₂[a, b] k,
        ContinuousLinearMap.adjoint (Ring.inverse (momJacobian a b σ)) u⟫ ^ 2 ∂μX).toNNReal)
      P' := by
  have h := hY (-ContinuousLinearMap.adjoint (Ring.inverse (momJacobian a b σ)) u)
  simp_rw [inner_neg_right, neg_sq] at h
  convert h using 2 with ω
  rw [inner_neg_left, ContinuousLinearMap.adjoint_inner_right]

/-- **The MLE limit has smaller variance than the moment-estimator limit in every direction.**
Let `Y₁` be the Gaussian vector of `tendstoInDistribution_countMLE` (projections
`N(0, E ⟪ψ, t⟫²)`) and `Y₂` that of `tendstoInDistribution_mom` (projections `N(0, E ⟪g, t⟫²)`).
Under the information identity and the differentiated unbiasedness of the moment equations
(`inner_inverse_countFisherInfo_le`), for every direction `u`
`Var ⟪I⁻¹ Y₁, u⟫ ≤ Var ⟪-J⁻¹ Y₂, u⟫`: the joint MLE is asymptotically at least as efficient as the
method-of-moments estimator. -/
theorem variance_inner_countMLE_limit_le {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hb : 0 < b)
    {μX : Measure ℕ} [IsProbabilityMeasure μX] (hk4 : Integrable (fun k : ℕ => (k : ℝ) ^ 4) μX)
    (hτ : σ / (a * (b + σ)) < ∫ k, trigammaIncrement a k ∂μX)
    (hinfo : ∀ z, ⟪countFisherInfo a b σ (∫ k, trigammaIncrement a k ∂μX) z, z⟫ =
      ∫ k, ⟪countScore σ !₂[a, b] k, z⟫ ^ 2 ∂μX)
    (hunb : ∀ x w, ⟪momJacobian a b σ x, w⟫ =
      -∫ k, ⟪countScore σ !₂[a, b] k, x⟫ * ⟪momEstFun σ !₂[a, b] k, w⟫ ∂μX)
    {Y₁ : Ω₁ → E₂} (hY₁ : ∀ t, HasLaw (fun ω => ⟪Y₁ ω, t⟫)
      (gaussianReal 0 (∫ k, ⟪countScore σ !₂[a, b] k, t⟫ ^ 2 ∂μX).toNNReal) P₁)
    {Y₂ : Ω₂ → E₂} (hY₂ : ∀ t, HasLaw (fun ω => ⟪Y₂ ω, t⟫)
      (gaussianReal 0 (∫ k, ⟪momEstFun σ !₂[a, b] k, t⟫ ^ 2 ∂μX).toNNReal) P₂) (u : E₂) :
    Var[fun ω => ⟪Ring.inverse (countFisherInfo a b σ (∫ k, trigammaIncrement a k ∂μX))
        (Y₁ ω), u⟫; P₁] ≤
      Var[fun ω => ⟪-Ring.inverse (momJacobian a b σ) (Y₂ ω), u⟫; P₂] := by
  have hY₁' : ∀ t, HasLaw (fun ω => ⟪Y₁ ω, t⟫) (gaussianReal 0
      (⟪countFisherInfo a b σ (∫ k, trigammaIncrement a k ∂μX) t, t⟫).toNNReal) P₁ :=
    fun t => by rw [hinfo]; exact hY₁ t
  rw [(hasLaw_inner_inverse_countFisherInfo ha hb hσ hτ hY₁' u).variance_eq,
    (hasLaw_inner_neg_inverse_momJacobian hY₂ u).variance_eq, variance_id_gaussianReal,
    variance_id_gaussianReal]
  exact NNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal
    (inner_inverse_countFisherInfo_le hσ ha hb hk4 hτ hinfo hunb u))

end MathlibExt.Biology.Omics.HierarchicalCount
