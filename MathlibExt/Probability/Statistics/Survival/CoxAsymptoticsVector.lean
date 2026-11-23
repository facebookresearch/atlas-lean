/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.CoxPartialLikelihood
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import MathlibExt.Probability.BoundedInProbability
public import MathlibExt.Probability.Distributions.GaussianConditioning
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Extrema

/-!
# Vector Cox regression: consistency and asymptotic normality (Andersen–Gill, `β ∈ ℝᵖ`)

This file is the vector analogue of `CoxAsymptotics` (scalar covariate), for covariate vectors
`xᵢ ∈ ℝᵖ`. For each sample size `n` the data `(Tᵢ, δᵢ, xᵢ)_{i < n}` are random,
`ω ↦ (T n ω, δ n ω, x n ω)`. Write
`ℓₙ = logPartialLikelihood`, `Uₙ = coxGradient` for the score vector (its gradient, see
`CoxPartialLikelihood`) and `Iₙ = coxInfoMatrix` for the observed information matrix
`∑_{i : δᵢ} Covᵢ(β)`, the sum of the `exp ⟪β, x⟫`-weighted risk-set covariance matrices
(`riskCov`). The Cox estimator `βhat n` is a maximizer of `ℓₙ` whenever one exists.

## The vector setup

`AndersenGillVector` collects the conditions at the true coefficient `β₀`, with a limiting
information function `info : ℝᵖ → ℝᵖˣᵖ` and radius `r > 0`:

* (score CLT) `Uₙ(β₀) / √n ⟶ Z` in distribution in `EuclideanSpace ℝ (Fin p)`;
* (uniform information) `Iₙ(b) / n → info(b)` entrywise, uniformly on `‖b - β₀‖ ≤ r`, in
  probability, stated as `P {ω | ∃ b, ‖b - β₀‖ ≤ r ∧ ∃ j k, η ≤ |Iₙ(b)ⱼₖ / n - info(b)ⱼₖ|} → 0`;
* (regularity) each entry of `info` is continuous at `β₀`, and `info(β₀)` is positive definite.

As in the scalar file, Andersen and Gill derive the two limit statements from their conditions
A–D by Rebolledo's martingale central limit theorem (under a Lindeberg condition on the score
martingale) and Lenglart's inequality; **that derivation is not formalized: the limit statements
are the hypotheses.** Gaussianity of the score limit, `Z ~ N(0, info(β₀))`, enters only the
normal-limit theorem.

## Main results

* `hasFDerivAt_coxGradient`: **the Jacobian of the score vector** is `-Iₙ(β)`
  (`hasFDerivAt_riskMeanVec`: the Jacobian of the risk-set mean is the risk-set covariance).
* `norm_coxGradient_sub_add_mulVec_le`: **matrix mean-value step**: if `Iₙ` is entrywise within
  `c` of `A` on a ball, then `‖Uₙ(b) - Uₙ(β₀) + A (b - β₀)‖ ≤ p c ‖b - β₀‖` there.
* `tendsto_measure_not_exists_isMaxOn_vector`: with probability tending to one `ℓₙ` has a
  maximizer.
* `tendstoInMeasure_coxMPLE_vector` (**consistency**, Andersen–Gill Theorem 3.2): `βhat n → β₀`
  in probability.
* `tendstoInDistribution_coxMPLE_vector_gaussian` (**asymptotic normality**, Andersen–Gill
  Theorem 3.3): `√n (βhat n - β₀) ⟶ Σ⁻¹ Z` with `Σ = info(β₀)`, and `Σ⁻¹ Z ~ N(0, Σ⁻¹)`
  (`hasLaw_toEuclideanLin_inv_multivariateGaussian`). `tendstoInDistribution_coxMPLE_vector` is
  the limit statement for an arbitrary score limit `Z`. Both assume `AEMeasurable (βhat n) P`.
* `tendstoInMeasure_coxInfoMatrix_coxMPLE_vector`: `Iₙ(βhat n) / n → info(β₀)` entrywise in
  probability.

The deterministic core: `antitone_coxGradient_dotProduct` (concavity along lines),
`coxGradient_add_dotProduct_neg` (a positive definite lower bound on `Iₙ / n` near `β₀` and a
small score make the score point inward on the sphere `‖b - β₀‖ = ε`),
`exists_isMaxOn_and_norm_sub_lt` and `norm_sub_lt_of_isMaxOn` (then a maximizer exists and every
maximizer lies in the ball), and `norm_sqrt_smul_sub_sub_le` (the one-step expansion
`√n (βhat - β₀) ≈ Σ⁻¹ (Uₙ(β₀) / √n)`). For `p = 1`, `coxGradient_one` and `coxInfoMatrix_one`
identify the score vector and information matrix with the scalar `coxScore` and
`coxInformation` of `CoxPartialLikelihood`, the quantities used by `CoxAsymptotics`.

Deterministic estimates use the sup norm of `Fin p → ℝ`; the distributional statements live in
`EuclideanSpace ℝ (Fin p)`, where Mathlib's `multivariateGaussian` is defined (`norm_le_norm_toLp`
and `norm_toLp_le` compare the two norms).

## Scope

The derivation of the score CLT and the uniform information limit from the counting-process
conditions (Rebolledo, Lenglart, the uniform law for `S⁽ᵏ⁾ / n`) is not formalized. A singular
limiting information matrix is excluded by `info_posDef`; no normal limit is claimed then.

## References

* P. K. Andersen and R. D. Gill, *Cox's regression model for counting processes: a large sample
  study*, Ann. Statist. 10 (1982), 1100–1120, Theorems 3.2 and 3.3.
* D. R. Cox, *Regression models and life-tables*, J. Roy. Statist. Soc. Ser. B 34 (1972),
  187–220.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.CoxAsymptoticsVector

open MeasureTheory ProbabilityTheory Filter Topology Finset Real Matrix
open MathlibExt.Probability.Statistics.CoxPartialLikelihood

/-! ### The information matrix and the Jacobian of the score vector -/

section Deterministic

variable {n p : ℕ}

/-- The `exp ⟪β, x⟫`-weighted covariance matrix of the covariate vectors over the risk set of
subject `i`: entry `(j, k)` is `∑ w x_j x_k / ∑ w - x̄ᵢⱼ x̄ᵢₖ` with `w_l = exp ⟪β, x_l⟫`. -/
noncomputable def riskCov (T : Fin n → ℝ) (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) (i : Fin n) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun j k => (∑ l ∈ riskSet T i, x l j * x l k * exp (β ⬝ᵥ x l)) /
      (∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l)) - riskMeanVec T x β i j * riskMeanVec T x β i k

/-- The observed information matrix of the Cox log partial likelihood,
`I(β) = ∑_{i : δᵢ} Covᵢ(β)`, the sum of the weighted risk-set covariance matrices over the
events. `hasFDerivAt_coxGradient` shows `-I(β)` is the Jacobian of the score vector. -/
noncomputable def coxInfoMatrix (T : Fin n → ℝ) (δ : Fin n → Bool) (x : Fin n → Fin p → ℝ)
    (β : Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  ∑ i with δ i = true, riskCov T x β i

/-- A square matrix as a continuous linear map on `Fin p → ℝ` (sup norm), `v ↦ A v`. -/
noncomputable def mulVecCLM (A : Matrix (Fin p) (Fin p) ℝ) : (Fin p → ℝ) →L[ℝ] (Fin p → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

@[simp]
theorem mulVecCLM_apply (A : Matrix (Fin p) (Fin p) ℝ) (v : Fin p → ℝ) :
    mulVecCLM A v = A *ᵥ v := by
  simp [mulVecCLM]

theorem mulVecCLM_sub (A B : Matrix (Fin p) (Fin p) ℝ) :
    mulVecCLM (A - B) = mulVecCLM A - mulVecCLM B := by
  ext v : 1
  simp [sub_mulVec]

theorem mulVecCLM_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin p) (Fin p) ℝ) :
    mulVecCLM (∑ i ∈ s, A i) = ∑ i ∈ s, mulVecCLM (A i) := by
  ext v j
  simp only [mulVecCLM_apply, FunLike.coe_sum, Finset.sum_apply, mulVec, dotProduct,
    Matrix.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

private lemma riskMeanVec_apply' (T : Fin n → ℝ) (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ)
    (i : Fin n) (j : Fin p) :
    riskMeanVec T x β i j =
      (∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l))⁻¹ * ∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l) * x l j := by
  simp [riskMeanVec, Finset.sum_apply]

private lemma cov_mulVec_aux (s : Finset (Fin n)) (w : Fin n → ℝ) (x : Fin n → Fin p → ℝ)
    (v : Fin p → ℝ) (j : Fin p) :
    ∑ k, ((∑ l ∈ s, x l j * x l k * w l) / (∑ l ∈ s, w l) -
        ((∑ l ∈ s, w l)⁻¹ * ∑ l ∈ s, w l * x l j) * ((∑ l ∈ s, w l)⁻¹ * ∑ l ∈ s, w l * x l k)) *
          v k =
      (∑ l ∈ s, w l)⁻¹ * ∑ l ∈ s, w l * (x l ⬝ᵥ v) * x l j -
        ((∑ l ∈ s, w l)⁻¹ * ∑ l ∈ s, w l * x l j) *
          ((∑ l ∈ s, w l)⁻¹ * ∑ l ∈ s, w l * (x l ⬝ᵥ v)) := by
  simp only [sub_mul, sum_sub_distrib]
  congr 1
  · simp only [dotProduct, div_eq_inv_mul, mul_sum, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun l _ => sum_congr rfl fun k _ => by ring
  · generalize (∑ l ∈ s, w l)⁻¹ * ∑ l ∈ s, w l * x l j = m
    simp only [dotProduct, mul_sum, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun l _ => sum_congr rfl fun k _ => by ring

/-- The weighted covariance matrix applied to `v`, entry `j`:
`∑ w (x ⬝ v) x_j / W - x̄ⱼ (x̄ ⬝ v)`. -/
theorem riskCov_mulVec_apply (T : Fin n → ℝ) (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) (i : Fin n)
    (v : Fin p → ℝ) (j : Fin p) :
    (riskCov T x β i *ᵥ v) j =
      (∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l))⁻¹ *
          ∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l) * (x l ⬝ᵥ v) * x l j -
        riskMeanVec T x β i j *
          ((∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l))⁻¹ *
            ∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l) * (x l ⬝ᵥ v)) := by
  change ∑ k, riskCov T x β i j k * v k = _
  simp only [riskCov, of_apply, riskMeanVec_apply']
  exact cov_mulVec_aux _ (fun l => exp (β ⬝ᵥ x l)) x v j

/-- **Jacobian of the risk-set mean vector**: the derivative of `β ↦ x̄ᵢ(β)` is the weighted
risk-set covariance matrix `Covᵢ(β)`. -/
theorem hasFDerivAt_riskMeanVec (T : Fin n → ℝ) (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ)
    (i : Fin n) :
    HasFDerivAt (fun β => riskMeanVec T x β i) (mulVecCLM (riskCov T x β i)) β := by
  have hW : HasFDerivAt (fun β => ∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l))
      (∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l) • Real.dotL (x l)) β :=
    HasFDerivAt.fun_sum fun l _ => (Real.hasFDerivAt_dotProduct (x l) β).exp
  have hS : HasFDerivAt (fun β => ∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l) • x l)
      (∑ l ∈ riskSet T i, (exp (β ⬝ᵥ x l) • Real.dotL (x l)).smulRight (x l)) β :=
    HasFDerivAt.fun_sum fun l _ => ((Real.hasFDerivAt_dotProduct (x l) β).exp).smul_const (x l)
  have hW0 : (∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l)) ≠ 0 :=
    (sum_pos (fun l _ => exp_pos _) (riskSet_nonempty T i)).ne'
  have hinv := (hasFDerivAt_inv hW0).comp β hW
  have h : HasFDerivAt (fun β => riskMeanVec T x β i) _ β := hinv.smul hS
  refine h.congr_fderiv ?_
  ext v j
  rw [mulVecCLM_apply, riskCov_mulVec_apply]
  simp only [_root_.add_apply, FunLike.coe_smul, FunLike.coe_sum, Pi.smul_apply, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, Real.dotL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, Pi.add_apply, Function.comp_apply]
  simp only [dotProduct_comm (x _) v, riskMeanVec_apply']
  generalize (∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l) * (v ⬝ᵥ x l) * x l j) = A
  generalize (∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l) * (v ⬝ᵥ x l)) = B
  generalize (∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l) * x l j) = C
  generalize (∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l)) = W at hW0 ⊢
  field_simp
  ring

/-- **Jacobian of the Cox score vector.** The Fréchet derivative of `β ↦ U(β)` is `-I(β)`, minus
the observed information matrix. -/
theorem hasFDerivAt_coxGradient (T : Fin n → ℝ) (δ : Fin n → Bool) (x : Fin n → Fin p → ℝ)
    (β : Fin p → ℝ) :
    HasFDerivAt (coxGradient T δ x) (-mulVecCLM (coxInfoMatrix T δ x β)) β := by
  have h : HasFDerivAt (fun β => ∑ i with δ i = true, (x i - riskMeanVec T x β i))
      (∑ i with δ i = true, (0 - mulVecCLM (riskCov T x β i))) β :=
    HasFDerivAt.fun_sum fun i _ =>
      (hasFDerivAt_const (x i) β).sub (hasFDerivAt_riskMeanVec T x β i)
  refine h.congr_fderiv ?_
  simp [coxInfoMatrix, mulVecCLM_sum, Finset.sum_neg_distrib]

/-- For one covariate (`p = 1`) the information matrix is the `1 × 1` matrix of the scalar
observed information `coxInformation`. -/
theorem coxInfoMatrix_one (T : Fin n → ℝ) (δ : Fin n → Bool) (z : Fin n → ℝ) (b : ℝ) :
    coxInfoMatrix T δ (fun i (_ : Fin 1) => z i) (fun _ => b) =
      Matrix.of fun _ _ => coxInformation T δ z b := by
  ext j k
  simp [coxInfoMatrix, Matrix.sum_apply, coxInformation, riskCov, riskVar, riskMean,
    riskMeanVec_apply, dotProduct, mul_comm b, sq]

/-! ### Concavity along lines -/

private lemma weighted_var_nonneg {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (w z : ι → ℝ)
    (hw : ∀ l, 0 < w l) :
    0 ≤ (∑ l ∈ s, z l ^ 2 * w l) / (∑ l ∈ s, w l) - ((∑ l ∈ s, z l * w l) / ∑ l ∈ s, w l) ^ 2 := by
  have hW : 0 < ∑ l ∈ s, w l := sum_pos (fun l _ => hw l) hs
  have hexp : ∀ m, ∑ l ∈ s, w l * (z l - m) ^ 2 =
      ∑ l ∈ s, z l ^ 2 * w l - 2 * m * ∑ l ∈ s, z l * w l + m ^ 2 * ∑ l ∈ s, w l := fun m => by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun l _ => by ring
  have key : (∑ l ∈ s, z l ^ 2 * w l) / (∑ l ∈ s, w l) - ((∑ l ∈ s, z l * w l) / ∑ l ∈ s, w l) ^ 2 =
      (∑ l ∈ s, w l * (z l - (∑ l ∈ s, z l * w l) / ∑ l ∈ s, w l) ^ 2) / ∑ l ∈ s, w l := by
    rw [hexp]
    generalize ∑ l ∈ s, z l ^ 2 * w l = A
    generalize ∑ l ∈ s, z l * w l = B
    generalize ∑ l ∈ s, w l = W at hW ⊢
    field_simp
    ring
  rw [key]
  exact div_nonneg (sum_nonneg fun l _ => mul_nonneg (hw l).le (sq_nonneg _)) hW.le

/-- The weighted risk-set variance of a linear covariate `⟪x, u⟫` is nonnegative. -/
theorem riskVarAlong_nonneg (T : Fin n → ℝ) (x : Fin n → Fin p → ℝ) (β u : Fin p → ℝ)
    (i : Fin n) : 0 ≤ riskVarAlong T x β u i := by
  have hm : riskMeanVec T x β i ⬝ᵥ u =
      (∑ l ∈ riskSet T i, (x l ⬝ᵥ u) * exp (β ⬝ᵥ x l)) / ∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l) := by
    simp only [riskMeanVec, smul_dotProduct, sum_dotProduct, smul_eq_mul]
    rw [inv_mul_eq_div]
    simp_rw [mul_comm (exp _)]
  rw [riskVarAlong, hm]
  exact weighted_var_nonneg _ (riskSet_nonempty T i) (fun l => exp (β ⬝ᵥ x l))
    (fun l => x l ⬝ᵥ u) fun l => exp_pos _

/-- **The score is antitone along every line** (concavity of the log partial likelihood):
`t ↦ ⟪U(β + t u), u⟫` is antitone. -/
theorem antitone_coxGradient_dotProduct (T : Fin n → ℝ) (δ : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) (β u : Fin p → ℝ) :
    Antitone fun t : ℝ => coxGradient T δ x (β + t • u) ⬝ᵥ u := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => coxGradient T δ x (β + t • u) ⬝ᵥ u)
      (-∑ i with δ i = true, riskVarAlong T x (β + t • u) u i) t := by
    intro t
    have h0 : HasDerivAt (fun s : ℝ => coxGradient T δ x ((β + t • u) + s • u) ⬝ᵥ u)
        (-∑ i with δ i = true, riskVarAlong T x (β + t • u) u i) (t - t) := by
      rw [sub_self]; exact hasDerivAt_coxGradient_dotProduct T δ x (β + t • u) u
    have hsub : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id' t).sub_const t
    have h1 := h0.comp (h := fun s : ℝ => s - t) t hsub
    convert h1 using 1
    · funext s
      simp only [Function.comp]
      congr 2
      rw [sub_smul]
      abel
    · ring
  refine antitone_of_deriv_nonpos (fun t => (hd t).differentiableAt) fun t => ?_
  rw [(hd t).deriv]
  exact neg_nonpos.2 (sum_nonneg fun i _ => riskVarAlong_nonneg T x _ u i)

/-! ### Norm estimates on `Fin p → ℝ` (sup norm) -/

/-- `|⟪a, b⟫| ≤ p ‖a‖ ‖b‖` for the sup norm. -/
theorem abs_dotProduct_le (a b : Fin p → ℝ) : |a ⬝ᵥ b| ≤ p * (‖a‖ * ‖b‖) := by
  calc |a ⬝ᵥ b| ≤ ∑ j, |a j * b j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin p, ‖a‖ * ‖b‖ := sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul (Real.norm_eq_abs (a j) ▸ norm_le_pi_norm a j)
          (Real.norm_eq_abs (b j) ▸ norm_le_pi_norm b j) (abs_nonneg _) (norm_nonneg _)
    _ = p * (‖a‖ * ‖b‖) := by simp

/-- An entrywise bound `|A j k| ≤ c` bounds `‖A v‖ ≤ p c ‖v‖` for the sup norm. -/
theorem norm_mulVec_le (A : Matrix (Fin p) (Fin p) ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ j k, |A j k| ≤ c) (v : Fin p → ℝ) : ‖A *ᵥ v‖ ≤ p * c * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  calc |(A *ᵥ v) j| = |∑ k, A j k * v k| := rfl
    _ ≤ ∑ k, |A j k * v k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin p, c * ‖v‖ := sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_mul (hA j k) (Real.norm_eq_abs (v k) ▸ norm_le_pi_norm v k) (abs_nonneg _) hc
    _ = p * c * ‖v‖ := by simp; ring

/-- Operator-norm form of `norm_mulVec_le`. -/
theorem norm_mulVecCLM_le (A : Matrix (Fin p) (Fin p) ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ j k, |A j k| ≤ c) : ‖mulVecCLM A‖ ≤ p * c :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => by
    rw [mulVecCLM_apply]; exact norm_mulVec_le A hc hA v

/-- **A positive definite matrix has a positive quadratic lower bound**: `λ ‖h‖² ≤ hᵀ S h` for
some `λ > 0` (sup norm). -/
theorem exists_pos_mul_sq_le_dotProduct_mulVec {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) :
    ∃ lam > 0, ∀ h : Fin p → ℝ, lam * ‖h‖ ^ 2 ≤ h ⬝ᵥ S *ᵥ h := by
  set q : (Fin p → ℝ) → ℝ := fun h => h ⬝ᵥ S *ᵥ h with hqdef
  have hq : Continuous q := by fun_prop
  have hpos : ∀ h ≠ 0, 0 < q h := fun h hh => by simpa using hS.dotProduct_mulVec_pos hh
  have hsmul : ∀ (c : ℝ) h, q (c • h) = c ^ 2 * q h := by
    intro c h; simp only [q, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring
  by_cases hne : (Metric.sphere (0 : Fin p → ℝ) 1).Nonempty
  · obtain ⟨h₀, hh₀, hmin⟩ := (isCompact_sphere 0 1).exists_isMinOn hne hq.continuousOn
    have h₀ne : h₀ ≠ 0 := by rintro rfl; simp at hh₀
    refine ⟨q h₀, hpos h₀ h₀ne, fun h => ?_⟩
    rcases eq_or_ne h 0 with rfl | hh
    · simp [q]
    have hn : 0 < ‖h‖ := norm_pos_iff.2 hh
    have hu : ‖h‖⁻¹ • h ∈ Metric.sphere (0 : Fin p → ℝ) 1 := by
      simp [norm_smul, hn.ne']
    have hle : q h₀ ≤ q (‖h‖⁻¹ • h) := hmin hu
    rw [hsmul] at hle
    calc q h₀ * ‖h‖ ^ 2 ≤ (‖h‖⁻¹ ^ 2 * q h) * ‖h‖ ^ 2 := by gcongr
      _ = q h := by field_simp
  · refine ⟨1, one_pos, fun h => ?_⟩
    have h0 : h = 0 := by
      by_contra hh
      exact hne ⟨‖h‖⁻¹ • h, by simp [norm_smul, (norm_pos_iff.2 hh).ne']⟩
    simp [h0]

/-- A quadratic lower bound `λ ‖h‖² ≤ hᵀ S h` gives `‖v‖ ≤ (p / λ) ‖S v‖`. -/
theorem norm_le_of_quadratic {S : Matrix (Fin p) (Fin p) ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hS : ∀ h : Fin p → ℝ, lam * ‖h‖ ^ 2 ≤ h ⬝ᵥ S *ᵥ h) (v : Fin p → ℝ) :
    ‖v‖ ≤ p / lam * ‖S *ᵥ v‖ := by
  have h1 := hS v
  have h2 : v ⬝ᵥ S *ᵥ v ≤ p * (‖v‖ * ‖S *ᵥ v‖) := (le_abs_self _).trans (abs_dotProduct_le _ _)
  rcases (norm_nonneg v).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
    nlinarith

/-! ### The matrix mean-value step -/

variable (T : Fin n → ℝ) (δ : Fin n → Bool) (x : Fin n → Fin p → ℝ)

/-- **Matrix mean-value step.** If the information matrix is entrywise within `c` of a fixed
matrix `A` on the ball `‖b - β₀‖ ≤ ε`, then on that ball
`‖U(b) - U(β₀) + A (b - β₀)‖ ≤ p c ‖b - β₀‖`. -/
theorem norm_coxGradient_sub_add_mulVec_le {β₀ b : Fin p → ℝ} {ε c : ℝ}
    (A : Matrix (Fin p) (Fin p) ℝ) (hc : 0 ≤ c)
    (hI : ∀ b' ∈ Metric.closedBall β₀ ε, ∀ j k, |coxInfoMatrix T δ x b' j k - A j k| ≤ c)
    (hb : b ∈ Metric.closedBall β₀ ε) :
    ‖coxGradient T δ x b - coxGradient T δ x β₀ + A *ᵥ (b - β₀)‖ ≤ p * c * ‖b - β₀‖ := by
  have hε : 0 ≤ ε := Metric.nonempty_closedBall.1 ⟨b, hb⟩
  have h := (convex_closedBall β₀ ε).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := coxGradient T δ x) (f' := fun b => -mulVecCLM (coxInfoMatrix T δ x b))
    (φ := -mulVecCLM A) (C := p * c)
    (fun b _ => (hasFDerivAt_coxGradient T δ x b).hasFDerivWithinAt)
    (fun b' hb' => by
      rw [neg_sub_neg, ← mulVecCLM_sub]
      exact norm_mulVecCLM_le _ hc fun j k => by
        rw [Matrix.sub_apply, abs_sub_comm]; exact hI b' hb' j k)
    (Metric.mem_closedBall_self hε) hb
  simpa [sub_neg_eq_add] using h

private lemma abs_sub_smul_le {S : Matrix (Fin p) (Fin p) ℝ} {η : ℝ} (hn : 0 < n)
    {M : Matrix (Fin p) (Fin p) ℝ} (hM : ∀ j k, |M j k / n - S j k| ≤ η) (j k : Fin p) :
    |M j k - ((n : ℝ) • S) j k| ≤ n * η := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Matrix.smul_apply, smul_eq_mul,
    show M j k - n * S j k = n * (M j k / n - S j k) by field_simp, abs_mul, abs_of_pos hn']
  exact mul_le_mul_of_nonneg_left (hM j k) hn'.le

/-- **The score points inward on a sphere.** If `I(b) / n` is entrywise within `η` of a matrix
`S` with `λ ‖h‖² ≤ hᵀ S h` on the ball `‖b - β₀‖ ≤ ε`, with `p² η ≤ λ / 2`, and
`p ‖U(β₀)‖ < n λ ε / 2`, then `⟪U(β₀ + h), h⟫ < 0` whenever `‖h‖ = ε`. -/
theorem coxGradient_add_dotProduct_neg {β₀ : Fin p → ℝ} {S : Matrix (Fin p) (Fin p) ℝ}
    {lam ε η : ℝ} (hn : 0 < n) (hS : ∀ h : Fin p → ℝ, lam * ‖h‖ ^ 2 ≤ h ⬝ᵥ S *ᵥ h)
    (hη : 0 ≤ η) (hpη : (p : ℝ) ^ 2 * η ≤ lam / 2)
    (hI : ∀ b ∈ Metric.closedBall β₀ ε, ∀ j k, |coxInfoMatrix T δ x b j k / n - S j k| ≤ η)
    (hU : p * ‖coxGradient T δ x β₀‖ < n * lam * ε / 2) {h : Fin p → ℝ} (hh : ‖h‖ = ε) :
    coxGradient T δ x (β₀ + h) ⬝ᵥ h < 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : β₀ + h ∈ Metric.closedBall β₀ ε := by simp [hh]
  have hmv := norm_coxGradient_sub_add_mulVec_le T δ x ((n : ℝ) • S) (by positivity)
    (fun b hb => abs_sub_smul_le hn (hI b hb)) hb
  rw [add_sub_cancel_left, hh] at hmv
  set R := coxGradient T δ x (β₀ + h) - coxGradient T δ x β₀ + ((n : ℝ) • S) *ᵥ h with hR
  have hdecomp : coxGradient T δ x (β₀ + h) ⬝ᵥ h =
      coxGradient T δ x β₀ ⬝ᵥ h - n * (h ⬝ᵥ S *ᵥ h) + R ⬝ᵥ h := by
    simp only [hR, add_dotProduct, sub_dotProduct, smul_mulVec, smul_dotProduct, smul_eq_mul,
      dotProduct_comm (S *ᵥ h) h]
    ring
  have h1 := (le_abs_self _).trans (abs_dotProduct_le (coxGradient T δ x β₀) h)
  have h2 := (le_abs_self _).trans (abs_dotProduct_le R h)
  have h3 := hS h
  rw [hh] at h1 h2 h3
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hU0 : 0 ≤ (p : ℝ) * ‖coxGradient T δ x β₀‖ := by positivity
  have hε : 0 ≤ ε := hh ▸ norm_nonneg h
  have hlε : 0 < n * lam * ε := by linarith
  have hε' : 0 < ε := by
    rcases hε.lt_or_eq with h' | h'
    · exact h'
    · rw [← h', mul_zero] at hlε; exact absurd hlε (lt_irrefl 0)
  have e1 : p * (‖coxGradient T δ x β₀‖ * ε) < n * lam * ε / 2 * ε := by
    rw [← mul_assoc]; exact mul_lt_mul_of_pos_right hU hε'
  have e2 : p * (‖R‖ * ε) ≤ p * (p * (n * η) * ε * ε) := by gcongr
  have e3 : p * (p * (n * η) * ε * ε) ≤ n * (lam / 2) * ε ^ 2 := by
    calc p * (p * (n * η) * ε * ε) = (p ^ 2 * η) * (n * ε ^ 2) := by ring
      _ ≤ lam / 2 * (n * ε ^ 2) := by gcongr
      _ = n * (lam / 2) * ε ^ 2 := by ring
  have e4 : n * (lam * ε ^ 2) ≤ n * (h ⬝ᵥ S *ᵥ h) := by gcongr
  nlinarith

/-! ### Existence and location of the maximizer -/

/-- A maximizer of the log partial likelihood is a root of the score vector. -/
theorem coxGradient_eq_zero_of_isMaxOn {b : Fin p → ℝ}
    (h : IsMaxOn (logPartialLikelihood T δ x) Set.univ b) : coxGradient T δ x b = 0 := by
  have h0 := (h.isLocalMax Filter.univ_mem).hasFDerivAt_eq_zero
    (hasFDerivAt_logPartialLikelihood T δ x b)
  funext j
  have := congrArg (fun L => L (Pi.single j 1)) h0
  simpa [Real.dotL_apply, single_dotProduct] using this

/-- **Existence of a maximizer near `β₀`.** If the score points inward on the sphere
`‖b - β₀‖ = ε`, the log partial likelihood has a global maximizer in the open ball. -/
theorem exists_isMaxOn_and_norm_sub_lt {β₀ : Fin p → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hin : ∀ h : Fin p → ℝ, ‖h‖ = ε → coxGradient T δ x (β₀ + h) ⬝ᵥ h < 0) :
    ∃ b, IsMaxOn (logPartialLikelihood T δ x) Set.univ b ∧ ‖b - β₀‖ < ε := by
  have hcont : Continuous (logPartialLikelihood T δ x) :=
    continuous_iff_continuousAt.2 fun b => (hasFDerivAt_logPartialLikelihood T δ x b).continuousAt
  obtain ⟨b, hb, hmax⟩ := (isCompact_closedBall β₀ ε).exists_isMaxOn
    (Metric.nonempty_closedBall.2 hε.le) hcont.continuousOn
  have hbε : ‖b - β₀‖ < ε := by
    rcases (show ‖b - β₀‖ ≤ ε by simpa [dist_eq_norm] using hb).lt_or_eq with hlt | heq
    · exact hlt
    exfalso
    have hseg : segment ℝ b (b + (β₀ - b)) ⊆ Metric.closedBall β₀ ε := by
      rw [add_sub_cancel]
      exact (convex_closedBall β₀ ε).segment_subset hb (Metric.mem_closedBall_self hε.le)
    have hle := hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos
      (hasFDerivAt_logPartialLikelihood T δ x b).hasFDerivWithinAt
      (mem_posTangentConeAt_of_segment_subset hseg)
    rw [Real.dotL_apply] at hle
    have hin' := hin (b - β₀) heq
    rw [add_sub_cancel] at hin'
    have : (β₀ - b) ⬝ᵥ coxGradient T δ x b = -(coxGradient T δ x b ⬝ᵥ (b - β₀)) := by
      rw [dotProduct_comm, ← neg_sub, dotProduct_neg]
    linarith
  refine ⟨b, fun y _ => ?_, hbε⟩
  have hnhds : Metric.closedBall β₀ ε ∈ 𝓝 b :=
    mem_nhds_iff.2 ⟨Metric.ball β₀ ε, Metric.ball_subset_closedBall, Metric.isOpen_ball,
      by simpa [dist_eq_norm] using hbε⟩
  exact IsMaxOn.of_isLocalMax_of_convex_univ (hmax.isLocalMax hnhds)
    (concaveOn_logPartialLikelihood T δ x) y

/-- **Location of every maximizer.** If the score points inward on the sphere `‖b - β₀‖ = ε`,
every global maximizer of the log partial likelihood lies in the open ball. -/
theorem norm_sub_lt_of_isMaxOn {β₀ : Fin p → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hin : ∀ h : Fin p → ℝ, ‖h‖ = ε → coxGradient T δ x (β₀ + h) ⬝ᵥ h < 0) {bh : Fin p → ℝ}
    (hbh : IsMaxOn (logPartialLikelihood T δ x) Set.univ bh) : ‖bh - β₀‖ < ε := by
  by_contra hge
  push Not at hge
  set d := bh - β₀ with hd_def
  have hd : 0 < ‖d‖ := hε.trans_le hge
  set t₀ := ε / ‖d‖ with ht₀_def
  have ht₀ : 0 < t₀ := div_pos hε hd
  have ht₁ : t₀ ≤ 1 := (div_le_one hd).2 hge
  have hk1 : coxGradient T δ x (β₀ + (1 : ℝ) • d) ⬝ᵥ d = 0 := by
    rw [one_smul, hd_def, add_sub_cancel, coxGradient_eq_zero_of_isMaxOn T δ x hbh,
      zero_dotProduct]
  have hkt := antitone_coxGradient_dotProduct T δ x β₀ d ht₁
  simp only at hkt
  have hnorm : ‖t₀ • d‖ = ε := by
    rw [norm_smul, Real.norm_of_nonneg ht₀.le, ht₀_def, div_mul_cancel₀ _ hd.ne']
  have hin' := hin _ hnorm
  rw [dotProduct_smul, smul_eq_mul] at hin'
  have hneg : coxGradient T δ x (β₀ + t₀ • d) ⬝ᵥ d < 0 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg ht₀.le hc]
  linarith

/-- **Deterministic core of asymptotic normality.** Let `bh` be a root of the score with
`‖bh - β₀‖ ≤ ε`, and let `I(b) / n` be entrywise within `η` of an invertible `S` with
`λ ‖h‖² ≤ hᵀ S h` on the ball, `p² η ≤ λ / 2`. Then
`‖√n (bh - β₀) - S⁻¹ (U(β₀) / √n)‖ ≤ (2 p³ η / λ²) ‖U(β₀) / √n‖`. -/
theorem norm_sqrt_smul_sub_sub_le {β₀ bh : Fin p → ℝ} {S : Matrix (Fin p) (Fin p) ℝ}
    {lam ε η : ℝ} (hn : 0 < n) (hlam : 0 < lam)
    (hS : ∀ h : Fin p → ℝ, lam * ‖h‖ ^ 2 ≤ h ⬝ᵥ S *ᵥ h) (hSinv : S * S⁻¹ = 1) (hη : 0 ≤ η)
    (hpη : (p : ℝ) ^ 2 * η ≤ lam / 2) (hroot : coxGradient T δ x bh = 0) (hb : ‖bh - β₀‖ ≤ ε)
    (hI : ∀ b ∈ Metric.closedBall β₀ ε, ∀ j k, |coxInfoMatrix T δ x b j k / n - S j k| ≤ η) :
    ‖√(n : ℝ) • (bh - β₀) - S⁻¹ *ᵥ ((√(n : ℝ))⁻¹ • coxGradient T δ x β₀)‖ ≤
      2 * p ^ 3 * η / lam ^ 2 * ‖(√(n : ℝ))⁻¹ • coxGradient T δ x β₀‖ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn'.le
  have hbmem : bh ∈ Metric.closedBall β₀ ε := by simpa [dist_eq_norm] using hb
  have hmv := norm_coxGradient_sub_add_mulVec_le T δ x ((n : ℝ) • S) (by positivity)
    (fun b hb => abs_sub_smul_le hn (hI b hb)) hbmem
  rw [hroot, zero_sub] at hmv
  set Y := √(n : ℝ) • (bh - β₀) with hY
  set V := (√(n : ℝ))⁻¹ • coxGradient T δ x β₀ with hV
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have key : ‖S *ᵥ Y - V‖ ≤ p * η * ‖Y‖ := by
    have heq : S *ᵥ Y - V =
        (√(n : ℝ))⁻¹ • (-coxGradient T δ x β₀ + ((n : ℝ) • S) *ᵥ (bh - β₀)) := by
      rw [hY, hV, mulVec_smul, smul_mulVec, smul_add, smul_neg, smul_smul,
        show (√(n : ℝ))⁻¹ * (n : ℝ) = √(n : ℝ) by rw [inv_mul_eq_div, div_eq_iff hsq.ne', hss]]
      abel
    rw [heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hsq.le), hY, norm_smul,
      Real.norm_of_nonneg hsq.le]
    calc (√(n : ℝ))⁻¹ * ‖-coxGradient T δ x β₀ + ((n : ℝ) • S) *ᵥ (bh - β₀)‖
        ≤ (√(n : ℝ))⁻¹ * (p * (n * η) * ‖bh - β₀‖) := by gcongr
      _ = p * η * (√(n : ℝ) * ‖bh - β₀‖) := by
        rw [show (p : ℝ) * (n * η) * ‖bh - β₀‖ =
          p * ((√(n : ℝ) * √(n : ℝ)) * η) * ‖bh - β₀‖ by rw [hss]]
        field_simp
  have hK := norm_le_of_quadratic hlam hS
  have hD : S *ᵥ (Y - S⁻¹ *ᵥ V) = S *ᵥ Y - V := by
    rw [mulVec_sub, mulVec_mulVec, hSinv, one_mulVec]
  have hDle : ‖Y - S⁻¹ *ᵥ V‖ ≤ p / lam * (p * η * ‖Y‖) :=
    (hK _).trans (by rw [hD]; gcongr)
  have hSV : ‖S⁻¹ *ᵥ V‖ ≤ p / lam * ‖V‖ := by
    have := hK (S⁻¹ *ᵥ V); rwa [mulVec_mulVec, hSinv, one_mulVec] at this
  have hYle : ‖Y‖ ≤ ‖Y - S⁻¹ *ᵥ V‖ + p / lam * ‖V‖ := by
    calc ‖Y‖ = ‖(Y - S⁻¹ *ᵥ V) + S⁻¹ *ᵥ V‖ := by rw [sub_add_cancel]
      _ ≤ ‖Y - S⁻¹ *ᵥ V‖ + ‖S⁻¹ *ᵥ V‖ := norm_add_le _ _
      _ ≤ _ := by gcongr
  set D := ‖Y - S⁻¹ *ᵥ V‖
  set a := (p : ℝ) ^ 2 * η / lam with ha_def
  set c := (p : ℝ) / lam * ‖V‖ with hc_def
  have ha : a ≤ 1 / 2 := by rw [ha_def, div_le_iff₀ hlam]; linarith
  have ha0 : 0 ≤ a := by positivity
  have hD0 : 0 ≤ D := norm_nonneg _
  have h1 : D ≤ a * (D + c) := by
    refine hDle.trans ?_
    rw [show (p : ℝ) / lam * (p * η * ‖Y‖) = a * ‖Y‖ by rw [ha_def]; field_simp]
    gcongr
  have h2 : D ≤ 2 * a * c := by nlinarith [mul_le_mul_of_nonneg_left ha hD0]
  calc D ≤ 2 * a * c := h2
    _ = 2 * p ^ 3 * η / lam ^ 2 * ‖V‖ := by rw [ha_def, hc_def]; field_simp

/-- A root of the score vector maximizes the log partial likelihood (concavity). -/
theorem isMaxOn_of_coxGradient_eq_zero {b : Fin p → ℝ} (h : coxGradient T δ x b = 0) :
    IsMaxOn (logPartialLikelihood T δ x) Set.univ b := by
  intro y _
  set d := y - b with hd
  set g : ℝ → ℝ := fun t => logPartialLikelihood T δ x (b + t • d) with hgdef
  have hg : ∀ t, HasDerivAt g (coxGradient T δ x (b + t • d) ⬝ᵥ d) t := fun t => by
    have := (hasFDerivAt_logPartialLikelihood T δ x (b + t • d)).comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const d).const_add b)
    rw [dotProduct_comm]
    simpa [Real.dotL_apply, Function.comp_def] using this
  have hanti := antitone_coxGradient_dotProduct T δ x b d
  have hmono : AntitoneOn g (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t _ => (hg t).continuousAt.continuousWithinAt)
      (fun t _ => (hg t).differentiableAt.differentiableWithinAt) fun t ht => ?_
    rw [interior_Ici] at ht
    rw [(hg t).deriv]
    have := hanti (le_of_lt ht)
    simp only [zero_smul, add_zero, h, zero_dotProduct] at this
    exact this
  have h01 := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_le_one
  simp only [hgdef, one_smul, zero_smul, add_zero, hd, add_sub_cancel] at h01
  exact h01

end Deterministic

/-! ### Sup norm versus Euclidean norm -/

section Norms

variable {p : ℕ}

/-- The sup norm is at most the Euclidean norm. -/
theorem norm_le_norm_toLp (v : Fin p → ℝ) : ‖v‖ ≤ ‖WithLp.toLp 2 v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => by
    simpa using PiLp.norm_apply_le (WithLp.toLp 2 v) j

/-- The Euclidean norm is at most `√p` times the sup norm. -/
theorem norm_toLp_le (v : Fin p → ℝ) : ‖WithLp.toLp 2 v‖ ≤ √(p : ℝ) * ‖v‖ := by
  rw [EuclideanSpace.norm_eq, show √(p : ℝ) * ‖v‖ = √(p * ‖v‖ ^ 2) by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ j, ‖(WithLp.toLp 2 v) j‖ ^ 2 ≤ ∑ _j : Fin p, ‖v‖ ^ 2 := sum_le_sum fun j _ => by
        gcongr; simpa using norm_le_pi_norm v j
    _ = p * ‖v‖ ^ 2 := by simp

end Norms

/-! ### Tightness and Gaussian helpers -/

section Probability

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- If `X n` converges in distribution, `P (c ≤ ‖X n‖ / √n) → 0` for every `c > 0`. -/
theorem tendsto_measure_le_norm_div_sqrt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {X : ℕ → Ω → E} {Z : Ω' → E} (h : TendstoInDistribution X atTop Z (fun _ ↦ P) P') {c : ℝ}
    (hc : 0 < c) :
    Tendsto (fun n : ℕ => P {ω | c ≤ ‖X n ω‖ / √(n : ℝ)}) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  obtain ⟨K, hK⟩ := exists_forall_measure_lt_norm_le_of_tendstoInDistribution h hκ
  have hsqrt : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually_gt_atTop (max K 0 / c)] with n hn
  refine le_trans (measure_mono fun ω (hω : c ≤ ‖X n ω‖ / √(n : ℝ)) => ?_) (hK n)
  have hpos : 0 < √(n : ℝ) := lt_of_le_of_lt (by positivity) hn
  rw [le_div_iff₀ hpos] at hω
  rw [div_lt_iff₀ hc] at hn
  change K < ‖X n ω‖
  nlinarith [le_max_left K 0, le_max_right K 0]

omit [IsProbabilityMeasure P'] in
/-- **Linear image of the score limit.** If `Z ~ N(0, S)` with `S` positive definite, then
`S⁻¹ Z ~ N(0, S⁻¹)`: the limit covariance of the estimator is the inverse information. -/
theorem hasLaw_toEuclideanLin_inv_multivariateGaussian {p : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) {Z : Ω' → EuclideanSpace ℝ (Fin p)}
    (hZ : HasLaw Z (multivariateGaussian 0 S) P') :
    HasLaw (fun ω => toEuclideanLin S⁻¹ (Z ω)) (multivariateGaussian 0 S⁻¹) P' := by
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hS.isUnit
  have hT : Sᵀ = S := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hS.isHermitian.eq
  have h := hasLaw_map (P := multivariateGaussian 0 S) (X := toEuclideanLin S⁻¹)
    (MetaMathlibExt.continuous_toEuclideanLin S⁻¹).aemeasurable
  rw [MetaMathlibExt.map_toEuclideanLin_multivariateGaussian _ _ hS.posSemidef, map_zero,
    nonsing_inv_mul _ hdet, one_mul, transpose_nonsing_inv, hT] at h
  exact h.comp hZ

end Probability

/-! ### The vector Andersen–Gill theorems -/

section AndersenGill

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {p : ℕ}

/-- **The vector Andersen–Gill conditions.** For each `n` the data are random:
`T n ω` (observed times), `δ n ω` (event indicators) and `x n ω` (covariate vectors in `ℝᵖ`).
The conditions at the true coefficient `β₀ ∈ ℝᵖ`, with a limiting information function
`info : ℝᵖ → ℝᵖˣᵖ` and a radius `r`:

* `score`: the normalized score vector converges in distribution,
  `Uₙ(β₀) / √n ⟶ Z` in `EuclideanSpace ℝ (Fin p)`. In Andersen–Gill this is Rebolledo's
  martingale central limit theorem for the score martingale under their Lindeberg condition;
  that derivation is not formalized, the limit statement is the hypothesis.
* `info_unif`: `Iₙ(b) / n → info(b)` entrywise, uniformly on the closed ball
  `‖b - β₀‖ ≤ r`, in probability (stated without measurability of the supremum).
* `info_cont`: every entry of `info` is continuous at `β₀`.
* `info_posDef`: the limiting information matrix `info β₀` is positive definite.
* `radius_pos`: `0 < r`.

Gaussianity of `Z` is a separate hypothesis of `tendstoInDistribution_coxMPLE_vector_gaussian`. -/
structure AndersenGillVector (P : Measure Ω) (P' : Measure Ω')
    (T : (n : ℕ) → Ω → Fin n → ℝ) (δ : (n : ℕ) → Ω → Fin n → Bool)
    (x : (n : ℕ) → Ω → Fin n → Fin p → ℝ) (β₀ : Fin p → ℝ) (Z : Ω' → EuclideanSpace ℝ (Fin p))
    (info : (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ) (r : ℝ) [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] : Prop where
  score : TendstoInDistribution
    (fun (n : ℕ) ω ↦ WithLp.toLp 2 ((√(n : ℝ))⁻¹ • coxGradient (T n ω) (δ n ω) (x n ω) β₀))
    atTop Z (fun _ ↦ P) P'
  info_unif : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Metric.closedBall β₀ r, ∃ j k,
    η ≤ |coxInfoMatrix (T n ω) (δ n ω) (x n ω) b j k / n - info b j k|}) atTop (𝓝 0)
  info_cont : ∀ j k, ContinuousAt (fun b => info b j k) β₀
  info_posDef : (info β₀).PosDef
  radius_pos : 0 < r

variable {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {T : (n : ℕ) → Ω → Fin n → ℝ} {δ : (n : ℕ) → Ω → Fin n → Bool}
  {x : (n : ℕ) → Ω → Fin n → Fin p → ℝ} {βhat : ℕ → Ω → Fin p → ℝ} {β₀ : Fin p → ℝ}
  {Z : Ω' → EuclideanSpace ℝ (Fin p)} {info : (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ} {r : ℝ}

/-- Continuity of the limiting information gives a radius on which it is entrywise within `η` of
`info β₀`. -/
private lemma exists_radius_info {η : ℝ} (hη : 0 < η)
    (hcont : ∀ j k, ContinuousAt (fun b => info b j k) β₀) :
    ∃ r₀ > 0, ∀ b : Fin p → ℝ, dist b β₀ < r₀ → ∀ j k, |info b j k - info β₀ j k| < η := by
  have h : ∀ᶠ b in 𝓝 β₀, ∀ j k, |info b j k - info β₀ j k| < η := by
    refine Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun k => ?_
    filter_upwards [(hcont j k).eventually (Metric.ball_mem_nhds (info β₀ j k) hη)] with b hb
    rwa [Real.dist_eq] at hb
  exact Metric.eventually_nhds_iff.1 h

/-- Off the two bad events, the normalized information is entrywise within `η` of `info β₀` on
the ball of radius `ε ≤ min (r₀ / 2) r`. -/
private lemma abs_info_sub_le {n : ℕ} {M : (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ}
    {η ε r₀ : ℝ} (hεr₀ : ε ≤ r₀ / 2) (hεr : ε ≤ r)
    (hr₀ : ∀ b : Fin p → ℝ, dist b β₀ < r₀ → ∀ j k, |info b j k - info β₀ j k| < η / 2)
    (hI : ∀ b ∈ Metric.closedBall β₀ r, ∀ j k, |M b j k / n - info b j k| < η / 2)
    (hr₀pos : 0 < r₀) :
    ∀ b ∈ Metric.closedBall β₀ ε, ∀ j k, |M b j k / n - info β₀ j k| ≤ η := by
  intro b hb j k
  have hbr : b ∈ Metric.closedBall β₀ r := Metric.closedBall_subset_closedBall hεr hb
  have h1 := hI b hbr j k
  have h2 := hr₀ b (lt_of_le_of_lt (Metric.mem_closedBall.1 hb) (by linarith)) j k
  calc |M b j k / n - info β₀ j k| ≤ |M b j k / n - info b j k| + |info b j k - info β₀ j k| :=
        abs_sub_le _ _ _
    _ ≤ η := by linarith

/-- `‖U‖ / n ≤ ‖U / √n‖₂ / √n`. -/
private lemma norm_div_le_norm_toLp_div {n : ℕ} (hn : 0 < n) (U : Fin p → ℝ) :
    ‖U‖ / n ≤ ‖WithLp.toLp 2 ((√(n : ℝ))⁻¹ • U)‖ / √(n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn'.le
  calc ‖U‖ / n = ‖U‖ / (√(n : ℝ) * √(n : ℝ)) := by rw [hss]
    _ = (√(n : ℝ))⁻¹ * ‖U‖ / √(n : ℝ) := by field_simp
    _ = ‖(√(n : ℝ))⁻¹ • U‖ / √(n : ℝ) := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hsq.le)]
    _ ≤ _ := by gcongr; exact norm_le_norm_toLp _

/-- **With probability tending to one the vector Cox estimator is a root of the score near
`β₀`.** Under the vector Andersen–Gill conditions, for every `ε > 0` the probability that
`βhat n` fails to be a root of the score vector within `ε` of `β₀` (sup norm) tends to zero. -/
theorem tendsto_measure_not_coxGradient_eq_zero_and_norm_sub_lt
    (hAG : AndersenGillVector P P' T δ x β₀ Z info r)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood (T n ω) (δ n ω) (x n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood (T n ω) (δ n ω) (x n ω)) Set.univ (βhat n ω))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => P {ω | ¬ (coxGradient (T n ω) (δ n ω) (x n ω) (βhat n ω) = 0 ∧
      ‖βhat n ω - β₀‖ < ε)}) atTop (𝓝 0) := by
  obtain ⟨lam, hlam, hq⟩ := exists_pos_mul_sq_le_dotProduct_mulVec hAG.info_posDef
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  set η := lam / (2 * ((p : ℝ) ^ 2 + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hpη : (p : ℝ) ^ 2 * η ≤ lam / 2 := by
    rw [hηdef, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨r₀, hr₀, hr₀'⟩ := exists_radius_info (half_pos hη) hAG.info_cont
  set ε' := min ε (min (r₀ / 2) r) with hε'def
  have hε'0 : 0 < ε' := lt_min hε (lt_min (by positivity) hAG.radius_pos)
  set c := lam * ε' / (2 * (p + 1)) with hcdef
  have hc : 0 < c := by positivity
  have hAB := (tendsto_measure_le_norm_div_sqrt (E := EuclideanSpace ℝ (Fin p)) hAG.score
    hc).add (hAG.info_unif (η / 2) (half_pos hη))
  rw [add_zero] at hAB
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hAB
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  rw [Set.mem_union]
  by_contra hbad
  rw [not_or] at hbad
  obtain ⟨hU, hI⟩ := hbad
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hU' : p * ‖coxGradient (T n ω) (δ n ω) (x n ω) β₀‖ < n * lam * ε' / 2 := by
    have h1 := norm_div_le_norm_toLp_div hn (coxGradient (T n ω) (δ n ω) (x n ω) β₀)
    have h2 : ¬ c ≤ ‖WithLp.toLp 2 ((√(n : ℝ))⁻¹ • coxGradient (T n ω) (δ n ω) (x n ω) β₀)‖ /
        √(n : ℝ) := hU
    have h3 := lt_of_le_of_lt h1 (not_le.1 h2)
    rw [div_lt_iff₀ hn'] at h3
    calc (p : ℝ) * ‖coxGradient (T n ω) (δ n ω) (x n ω) β₀‖
        ≤ (p + 1) * ‖coxGradient (T n ω) (δ n ω) (x n ω) β₀‖ := by gcongr; linarith
      _ < (p + 1) * (c * n) := by gcongr
      _ = n * lam * ε' / 2 := by rw [hcdef]; field_simp
  have hI' := abs_info_sub_le (M := coxInfoMatrix (T n ω) (δ n ω) (x n ω)) (n := n) (ε := ε')
    ((min_le_right _ _).trans (min_le_left _ _)) ((min_le_right _ _).trans (min_le_right _ _))
    hr₀' (fun b hb j k => lt_of_not_ge fun h => hI ⟨b, hb, j, k, h⟩) hr₀
  have hin : ∀ h : Fin p → ℝ, ‖h‖ = ε' →
      coxGradient (T n ω) (δ n ω) (x n ω) (β₀ + h) ⬝ᵥ h < 0 := fun h hh =>
    coxGradient_add_dotProduct_neg (T n ω) (δ n ω) (x n ω) hn hq hη.le hpη hI' hU' hh
  obtain ⟨b, hbmax, -⟩ := exists_isMaxOn_and_norm_sub_lt (T n ω) (δ n ω) (x n ω) hε'0 hin
  have hmax := hβhat n ω ⟨b, hbmax⟩
  exact hω ⟨coxGradient_eq_zero_of_isMaxOn _ _ _ hmax,
    lt_of_lt_of_le (norm_sub_lt_of_isMaxOn _ _ _ hε'0 hin hmax) (min_le_left _ _)⟩

/-- **Existence of the vector Cox estimator with probability tending to one.** -/
theorem tendsto_measure_not_exists_isMaxOn_vector
    (hAG : AndersenGillVector P P' T δ x β₀ Z info r) :
    Tendsto (fun n : ℕ => P {ω | ¬ ∃ b,
      IsMaxOn (logPartialLikelihood (T n ω) (δ n ω) (x n ω)) Set.univ b}) atTop (𝓝 0) := by
  classical
  let βsel : ℕ → Ω → Fin p → ℝ := fun n ω =>
    if h : ∃ b, IsMaxOn (logPartialLikelihood (T n ω) (δ n ω) (x n ω)) Set.univ b
    then h.choose else 0
  have hsel : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood (T n ω) (δ n ω) (x n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood (T n ω) (δ n ω) (x n ω)) Set.univ (βsel n ω) :=
    fun n ω h => by simp only [βsel, h, ↓reduceDIte]; exact h.choose_spec
  have hG := tendsto_measure_not_coxGradient_eq_zero_and_norm_sub_lt hAG hsel one_pos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hG (fun _ => zero_le)
    fun n => measure_mono fun ω hω hgood =>
      hω ⟨βsel n ω, isMaxOn_of_coxGradient_eq_zero _ _ _ hgood.1⟩

/-- **Consistency of the vector Cox estimator** (Andersen–Gill 1982, Theorem 3.2, `β ∈ ℝᵖ`).
Let `βhat n` be a maximizer of the log partial likelihood whenever one exists. Under the vector
Andersen–Gill conditions, `βhat n → β₀` in probability. -/
theorem tendstoInMeasure_coxMPLE_vector (hAG : AndersenGillVector P P' T δ x β₀ Z info r)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood (T n ω) (δ n ω) (x n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood (T n ω) (δ n ω) (x n ω)) Set.univ (βhat n ω)) :
    TendstoInMeasure P βhat atTop (fun _ => β₀) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_measure_not_coxGradient_eq_zero_and_norm_sub_lt hAG hβhat hε)
    (fun _ => zero_le) fun n => measure_mono fun ω hω hgood => ?_
  have h : ε ≤ dist (βhat n ω) β₀ := hω
  rw [dist_eq_norm] at h
  exact absurd hgood.2 (not_lt.2 h)

/-- **The vector Cox estimator is asymptotically `I⁻¹ Z`.** Under the vector Andersen–Gill
conditions and measurability of the estimator, `√n (βhat n - β₀) ⟶ info(β₀)⁻¹ Z` in distribution
in `EuclideanSpace ℝ (Fin p)`, where `Z` is the limit of `Uₙ(β₀) / √n`. No Gaussianity is used;
see `tendstoInDistribution_coxMPLE_vector_gaussian` for the normal limit. -/
theorem tendstoInDistribution_coxMPLE_vector (hAG : AndersenGillVector P P' T δ x β₀ Z info r)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood (T n ω) (δ n ω) (x n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood (T n ω) (δ n ω) (x n ω)) Set.univ (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ WithLp.toLp 2 (√(n : ℝ) • (βhat n ω - β₀))) atTop
      (fun ω => toEuclideanLin (info β₀)⁻¹ (Z ω)) (fun _ ↦ P) P' := by
  set S := info β₀ with hSdef
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hAG.info_posDef.isUnit
  have hSinv : S * S⁻¹ = 1 := mul_nonsing_inv _ hdet
  obtain ⟨lam, hlam, hq⟩ := exists_pos_mul_sq_le_dotProduct_mulVec hAG.info_posDef
  set Sc : ℕ → Ω → EuclideanSpace ℝ (Fin p) := fun n ω =>
    WithLp.toLp 2 ((√(n : ℝ))⁻¹ • coxGradient (T n ω) (δ n ω) (x n ω) β₀) with hScdef
  have hX := hAG.score.continuous_comp (MetaMathlibExt.continuous_toEuclideanLin S⁻¹)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hX ?_ fun n =>
    (PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable
      (((hβhat_meas n).sub_const β₀).fun_const_smul (√(n : ℝ)))
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  obtain ⟨K, hK⟩ := exists_forall_measure_lt_norm_le_of_tendstoInDistribution hAG.score
    (ENNReal.half_pos hκ.ne')
  set M := max K 0 + 1 with hMdef
  have hM : 0 < M := by linarith [le_max_right K 0]
  have hMn : ∀ n, P {ω | M ≤ ‖Sc n ω‖} ≤ κ / 2 := fun n =>
    le_trans (measure_mono fun ω (hω : M ≤ ‖Sc n ω‖) =>
      show K < ‖Sc n ω‖ by linarith [le_max_left K 0]) (hK n)
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  set C := 2 * (√(p : ℝ) + 1) * ((p : ℝ) ^ 3 + 1) / lam ^ 2 with hCdef
  have hC : 0 < C := by positivity
  set η := min (lam / (2 * ((p : ℝ) ^ 2 + 1))) (ε / (2 * C * M)) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hpη : (p : ℝ) ^ 2 * η ≤ lam / 2 := by
    refine (mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg _)).trans ?_
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨r₀, hr₀, hr₀'⟩ := exists_radius_info (half_pos hη) hAG.info_cont
  set r₁ := min (r₀ / 2) r with hr₁def
  have hr₁ : 0 < r₁ := lt_min (by positivity) hAG.radius_pos
  have hGB := (tendsto_measure_not_coxGradient_eq_zero_and_norm_sub_lt hAG hβhat hr₁).add
    (hAG.info_unif (η / 2) (half_pos hη))
  rw [add_zero] at hGB
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hGB) (κ / 2) (ENNReal.half_pos hκ.ne'),
    eventually_gt_atTop 0] with n hn' hn0
  let A : Set Ω := {ω | M ≤ ‖Sc n ω‖}
  let B : Set Ω := {ω | ¬ (coxGradient (T n ω) (δ n ω) (x n ω) (βhat n ω) = 0 ∧
    ‖βhat n ω - β₀‖ < r₁)}
  let C' : Set Ω := {ω | ∃ b ∈ Metric.closedBall β₀ r, ∃ j k,
    η / 2 ≤ |coxInfoMatrix (T n ω) (δ n ω) (x n ω) b j k / n - info b j k|}
  have hBC : P B + P C' ≤ κ / 2 := hn'
  refine le_trans (measure_mono (t := A ∪ (B ∪ C')) ?_) (le_trans
    ((measure_union_le _ _).trans (add_le_add_right (measure_union_le _ _) _))
    (le_trans (add_le_add (hMn n) hBC) (ENNReal.add_halves κ).le))
  intro ω hω
  rw [Set.mem_union, Set.mem_union]
  by_contra hbad
  simp only [not_or] at hbad
  obtain ⟨hS, hroot, hI⟩ := hbad
  have hS' : ‖Sc n ω‖ < M := lt_of_not_ge hS
  have hroot' : coxGradient (T n ω) (δ n ω) (x n ω) (βhat n ω) = 0 ∧ ‖βhat n ω - β₀‖ < r₁ :=
    not_not.1 hroot
  have hI' := abs_info_sub_le (M := coxInfoMatrix (T n ω) (δ n ω) (x n ω)) (n := n) (ε := r₁)
    (min_le_left _ _) (min_le_right _ _) hr₀'
    (fun b hb j k => lt_of_not_ge fun h => hI ⟨b, hb, j, k, h⟩) hr₀
  have hbound := norm_sqrt_smul_sub_sub_le (T n ω) (δ n ω) (x n ω) hn0 hlam hq hSinv hη.le hpη
    hroot'.1 hroot'.2.le hI'
  set D := √(n : ℝ) • (βhat n ω - β₀) -
    S⁻¹ *ᵥ ((√(n : ℝ))⁻¹ • coxGradient (T n ω) (δ n ω) (x n ω) β₀) with hDdef
  have hdiff : (fun ω ↦ WithLp.toLp 2 (√(n : ℝ) • (βhat n ω - β₀))) ω -
      ((toEuclideanLin S⁻¹) ∘ Sc n) ω = WithLp.toLp 2 D := rfl
  have hlt : ‖(fun ω ↦ WithLp.toLp 2 (√(n : ℝ) • (βhat n ω - β₀))) ω -
      ((toEuclideanLin S⁻¹) ∘ Sc n) ω‖ < ε := by
    rw [hdiff]
    calc ‖WithLp.toLp 2 D‖ ≤ √(p : ℝ) * ‖D‖ := norm_toLp_le D
      _ ≤ √(p : ℝ) * (2 * p ^ 3 * η / lam ^ 2 *
          ‖(√(n : ℝ))⁻¹ • coxGradient (T n ω) (δ n ω) (x n ω) β₀‖) := by gcongr
      _ ≤ √(p : ℝ) * (2 * p ^ 3 * η / lam ^ 2 * ‖Sc n ω‖) := by
          gcongr; exact norm_le_norm_toLp _
      _ = 2 * η / lam ^ 2 * (√(p : ℝ) * p ^ 3 * ‖Sc n ω‖) := by ring
      _ ≤ 2 * η / lam ^ 2 * ((√(p : ℝ) + 1) * ((p : ℝ) ^ 3 + 1) * M) := by
          gcongr
          all_goals linarith
      _ = C * η * M := by rw [hCdef]; ring
      _ ≤ C * (ε / (2 * C * M)) * M := by gcongr; exact min_le_right _ _
      _ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε
  simp only [Set.mem_ofPred_eq, Pi.sub_apply, Pi.zero_apply, sub_zero] at hω
  exact (not_le.2 hlt) hω

/-- **Asymptotic normality of the vector Cox estimator** (Andersen–Gill 1982, Theorem 3.3,
`β ∈ ℝᵖ`). Let `βhat n` be a measurable maximizer of the log partial likelihood whenever one
exists. Under the vector Andersen–Gill conditions, if the score limit is Gaussian,
`Z ~ N(0, Σ)` with `Σ = info(β₀)` the limiting information matrix, then
`√n (βhat n - β₀) ⟶ Σ⁻¹ Z` in distribution and `Σ⁻¹ Z ~ N(0, Σ⁻¹)`: the asymptotic covariance is
the inverse of the information matrix. This file does not show that the full hypothesis set
(the conditions together with a nondegenerate Gaussian score limit) is satisfiable. -/
theorem tendstoInDistribution_coxMPLE_vector_gaussian
    (hAG : AndersenGillVector P P' T δ x β₀ Z info r)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood (T n ω) (δ n ω) (x n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood (T n ω) (δ n ω) (x n ω)) Set.univ (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) P)
    (hZ : HasLaw Z (multivariateGaussian 0 (info β₀)) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ WithLp.toLp 2 (√(n : ℝ) • (βhat n ω - β₀))) atTop
      (fun ω => toEuclideanLin (info β₀)⁻¹ (Z ω)) (fun _ ↦ P) P' ∧
    HasLaw (fun ω => toEuclideanLin (info β₀)⁻¹ (Z ω)) (multivariateGaussian 0 (info β₀)⁻¹) P' :=
  ⟨tendstoInDistribution_coxMPLE_vector hAG hβhat hβhat_meas,
    hasLaw_toEuclideanLin_inv_multivariateGaussian hAG.info_posDef hZ⟩

/-- **Consistency of the normalized information matrix at the estimator.** Under the vector
Andersen–Gill conditions, every entry of `Iₙ(βhat n) / n` converges in probability to the
corresponding entry of `info(β₀)`. -/
theorem tendstoInMeasure_coxInfoMatrix_coxMPLE_vector
    (hAG : AndersenGillVector P P' T δ x β₀ Z info r)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood (T n ω) (δ n ω) (x n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood (T n ω) (δ n ω) (x n ω)) Set.univ (βhat n ω))
    (j k : Fin p) :
    TendstoInMeasure P
      (fun n ω => coxInfoMatrix (T n ω) (δ n ω) (x n ω) (βhat n ω) j k / n) atTop
      (fun _ => info β₀ j k) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  obtain ⟨r₀, hr₀, hr₀'⟩ := exists_radius_info (half_pos (half_pos hε)) hAG.info_cont
  set r₁ := min (r₀ / 2) r with hr₁def
  have hr₁ : 0 < r₁ := lt_min (by positivity) hAG.radius_pos
  have hGB := (tendsto_measure_not_coxGradient_eq_zero_and_norm_sub_lt hAG hβhat hr₁).add
    (hAG.info_unif (ε / 2 / 2) (half_pos (half_pos hε)))
  rw [add_zero] at hGB
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hGB (fun _ => zero_le)
    fun n => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  rw [Set.mem_union]
  by_contra hbad
  rw [not_or] at hbad
  obtain ⟨hroot, hI⟩ := hbad
  have hroot' : coxGradient (T n ω) (δ n ω) (x n ω) (βhat n ω) = 0 ∧ ‖βhat n ω - β₀‖ < r₁ :=
    not_not.1 hroot
  have hI' := abs_info_sub_le (M := coxInfoMatrix (T n ω) (δ n ω) (x n ω)) (n := n) (ε := r₁)
    (η := ε / 2) (min_le_left _ _) (min_le_right _ _) hr₀'
    (fun b hb j k => lt_of_not_ge fun h => hI ⟨b, hb, j, k, h⟩) hr₀
  have hb : βhat n ω ∈ Metric.closedBall β₀ r₁ := by
    simpa [dist_eq_norm] using hroot'.2.le
  have h1 := hI' _ hb j k
  have hω' : ε ≤ dist (coxInfoMatrix (T n ω) (δ n ω) (x n ω) (βhat n ω) j k / n)
      (info β₀ j k) := hω
  rw [Real.dist_eq] at hω'
  linarith

end AndersenGill

end MathlibExt.Probability.Statistics.CoxAsymptoticsVector
