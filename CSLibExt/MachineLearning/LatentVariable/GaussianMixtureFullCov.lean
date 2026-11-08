/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.ExpectationMaximization
public import MathlibExt.Probability.Distributions.GaussianMLE

/-!
# EM for Gaussian mixtures with full covariances

The EM algorithm for a mixture of `K` Gaussians with full covariance matrices in
`EuclideanSpace ℝ (Fin d)` (Bishop, *Pattern Recognition and Machine Learning*, Section 9.2.2), as
an instance of the generic EM of `LatentVariable/ExpectationMaximization.lean`. The component
density is the multivariate Gaussian density `MetaMathlibExt.multivariateGaussianPDFReal`, proved
in MathlibExt to be the density of Mathlib's `multivariateGaussian`.

Main results:

* `joint` (`π k N(x | μ k, Σ k)`) on `ValidParams` (positive weights summing to one, positive
  definite covariances); `resp`, the E-step responsibilities, is the posterior `P(z = k | xₙ)`.
* The M-step `mStep`: `π k' = N k / N` (`mass`), `μ k'` the responsibility-weighted mean
  (`newMean`), and **`Σ k'` the responsibility-weighted sample covariance** (`newCov`), with
  MathlibExt's `weightedMean` and `weightedScatter`. On data in general position
  (`SpansAffinely`: not all in an affine hyperplane) the covariance update is positive definite
  (`newCov_posDef`), so the M-step is valid (`mStep_valid`, `emStep`).
* `compTerm_le`: **the mean and covariance updates maximize each component term of `Q`** over all
  means and positive definite covariances: the weighted Gaussian MLE
  `MetaMathlibExt.sum_mul_log_multivariateGaussianPDFReal_le` with the responsibilities as
  weights.
* `emQ_le_emStep`: the M-step maximizes `Q(· | θ)` over all valid parameters;
  `logLik_le_emStep`, `logLik_iterate_emStep_monotone`: **each EM step does not decrease the
  log-likelihood**, and the log-likelihood is monotone along the EM iterates.

`LatentVariable/GaussianMixture.lean` treats the isotropic case `Σ k = σ k² I`.

## Cost model

No running-time model: the subject is the likelihood, over the reals.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.LatentVariable.GaussianMixtureFullCov

open Real Matrix WithLp MetaMathlibExt
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization
open scoped RealInnerProductSpace

variable {d K N : ℕ}

/-! ## The model -/

/-- Parameters of a `K`-component Gaussian mixture in `d` dimensions with full covariances. -/
structure Params (d K : ℕ) where
  /-- The mixing weights `π k`. -/
  weight : Fin K → ℝ
  /-- The component means `μ k`. -/
  mean : Fin K → EuclideanSpace ℝ (Fin d)
  /-- The component covariances `Σ k`. -/
  cov : Fin K → Matrix (Fin d) (Fin d) ℝ

/-- Valid parameters: positive weights summing to one, positive definite covariances. -/
structure Params.Valid (θ : Params d K) : Prop where
  weight_pos : ∀ k, 0 < θ.weight k
  weight_sum : ∑ k, θ.weight k = 1
  cov_posDef : ∀ k, (θ.cov k).PosDef

/-- The valid parameters, the parameter space of EM. -/
abbrev ValidParams (d K : ℕ) := {θ : Params d K // θ.Valid}

/-- The joint density `p_θ(x, k) = π k N(x | μ k, Σ k)`, with Mathlib's multivariate Gaussian
density (`MetaMathlibExt.multivariateGaussianPDFReal`). -/
noncomputable def joint (θ : ValidParams d K) (x : EuclideanSpace ℝ (Fin d)) (k : Fin K) : ℝ :=
  θ.1.weight k * multivariateGaussianPDFReal (θ.1.mean k) (θ.1.cov k) x

theorem joint_pos (θ : ValidParams d K) (x : EuclideanSpace ℝ (Fin d)) (k : Fin K) :
    0 < joint θ x k :=
  mul_pos (θ.2.weight_pos k) (multivariateGaussianPDFReal_pos _ (θ.2.cov_posDef k) x)

/-- The responsibilities `r n k = P(z = k | xₙ)` (the E-step): the posterior of the mixture. -/
noncomputable def resp (θ : ValidParams d K) (x : EuclideanSpace ℝ (Fin d)) (k : Fin K) : ℝ :=
  posterior joint θ x k

theorem resp_pos (θ : ValidParams d K) (x : EuclideanSpace ℝ (Fin d)) (k : Fin K) :
    0 < resp θ x k :=
  div_pos (joint_pos θ x k) (Finset.sum_pos (fun k _ => joint_pos θ x k) ⟨k, Finset.mem_univ k⟩)

theorem nonempty_of_valid (θ : ValidParams d K) : Nonempty (Fin K) := by
  by_contra h
  have : IsEmpty (Fin K) := not_nonempty_iff.1 h
  have := θ.2.weight_sum
  simp at this

theorem sum_resp (θ : ValidParams d K) (x : EuclideanSpace ℝ (Fin d)) : ∑ k, resp θ x k = 1 := by
  have := nonempty_of_valid θ
  exact (isDist_posterior (fun θ x k => joint_pos θ x k) θ x).2

/-! ## The M-step -/

variable (xs : Fin N → EuclideanSpace ℝ (Fin d))

/-- The effective number of points of component `k`, `N k = ∑ n, r n k`. -/
noncomputable def mass (θ : ValidParams d K) (k : Fin K) : ℝ := ∑ n, resp θ (xs n) k

/-- The responsibility-weighted mean `μ k' = (∑ n, r n k xₙ) / N k`. -/
noncomputable def newMean (θ : ValidParams d K) (k : Fin K) : EuclideanSpace ℝ (Fin d) :=
  weightedMean (fun n => resp θ (xs n) k) xs

/-- The covariance update: the responsibility-weighted sample covariance
`(∑ n, r n k (xₙ - μ k') (xₙ - μ k')ᵀ) / N k` about the weighted mean. -/
noncomputable def newCov (θ : ValidParams d K) (k : Fin K) : Matrix (Fin d) (Fin d) ℝ :=
  weightedScatter (fun n => resp θ (xs n) k) xs (newMean xs θ k)

/-- The M-step: `π k' = N k / N`, `μ k'` the weighted mean, `Σ k'` the weighted sample
covariance. -/
noncomputable def mStep (θ : ValidParams d K) : Params d K where
  weight k := mass xs θ k / N
  mean := newMean xs θ
  cov := newCov xs θ

/-! ## Data in general position -/

variable {xs} in
/-- Data in general position: at least one point, and not all contained in an affine hyperplane
(for every nonzero direction `v`, the projections `⟪v, xₙ⟫` are not all equal). Then every
responsibility-weighted sample covariance is positive definite (`newCov_posDef`). -/
structure SpansAffinely (xs : Fin N → EuclideanSpace ℝ (Fin d)) : Prop where
  pos : 0 < N
  spans : ∀ v : EuclideanSpace ℝ (Fin d), v ≠ 0 → ∃ n n', ⟪v, xs n⟫ ≠ ⟪v, xs n'⟫

theorem mass_pos (hN : 0 < N) (θ : ValidParams d K) (k : Fin K) : 0 < mass xs θ k :=
  Finset.sum_pos (fun n _ => resp_pos θ (xs n) k) ⟨⟨0, hN⟩, Finset.mem_univ _⟩

theorem sum_mass (θ : ValidParams d K) : ∑ k, mass xs θ k = N := by
  simp only [mass]
  rw [Finset.sum_comm]
  simp [sum_resp]

/-- **The covariance update is positive definite** on data in general position. -/
theorem newCov_posDef {xs : Fin N → EuclideanSpace ℝ (Fin d)} (hx : SpansAffinely xs)
    (θ : ValidParams d K) (k : Fin K) : (newCov xs θ k).PosDef :=
  weightedScatter_posDef (fun n => resp_pos θ (xs n) k) hx.spans _

theorem mStep_valid {xs : Fin N → EuclideanSpace ℝ (Fin d)} (hx : SpansAffinely xs)
    (θ : ValidParams d K) : (mStep xs θ).Valid where
  weight_pos k := div_pos (mass_pos xs hx.pos θ k) (by exact_mod_cast hx.pos)
  weight_sum := by
    simp only [mStep]
    rw [← Finset.sum_div, sum_mass, div_self (by exact_mod_cast hx.pos.ne')]
  cov_posDef k := newCov_posDef hx θ k

/-- One EM step for the full-covariance Gaussian mixture (E-step then M-step), on data in general
position. -/
noncomputable def emStep (hx : SpansAffinely xs) (θ : ValidParams d K) : ValidParams d K :=
  ⟨mStep xs θ, mStep_valid hx θ⟩

/-! ## The M-step maximizes `Q` -/

/-- The component term of `Q`: `∑ n, r n k log N(xₙ | μ, S)`. -/
noncomputable def compTerm (θ : ValidParams d K) (k : Fin K) (μ : EuclideanSpace ℝ (Fin d))
    (S : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ n, resp θ (xs n) k * log (multivariateGaussianPDFReal μ S (xs n))

/-- `Q(θ' | θ)` splits into a weights term and one term per component. -/
theorem emQ_eq (θ' θ : ValidParams d K) :
    emQ joint xs θ' θ = ∑ k, (mass xs θ k * log (θ'.1.weight k) +
      compTerm xs θ k (θ'.1.mean k) (θ'.1.cov k)) := by
  have hlog : ∀ n k, log (joint θ' (xs n) k) = log (θ'.1.weight k) +
      log (multivariateGaussianPDFReal (θ'.1.mean k) (θ'.1.cov k) (xs n)) := fun n k =>
    log_mul (θ'.2.weight_pos k).ne' (multivariateGaussianPDFReal_pos _ (θ'.2.cov_posDef k) _).ne'
  simp only [emQ, hlog, mul_add, Finset.sum_add_distrib, mass, compTerm]
  rw [Finset.sum_comm (f := fun n k => posterior joint θ (xs n) k * log (θ'.1.weight k)),
    Finset.sum_comm (f := fun n k => posterior joint θ (xs n) k *
      log (multivariateGaussianPDFReal (θ'.1.mean k) (θ'.1.cov k) (xs n)))]
  simp only [Finset.sum_mul, resp]

/-- **The mean and covariance updates maximize each component term**: over all means `μ` and
positive definite covariances `S`, `∑ n, r n k log N(xₙ | μ, S)` is largest at the weighted mean
and the weighted sample covariance (the log-determinant trace inequality
`Matrix.PosDef.log_det_mul_le_trace`). -/
theorem compTerm_le {xs : Fin N → EuclideanSpace ℝ (Fin d)} (hx : SpansAffinely xs)
    (θ : ValidParams d K) (k : Fin K) (μ : EuclideanSpace ℝ (Fin d))
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    compTerm xs θ k μ S ≤ compTerm xs θ k (newMean xs θ k) (newCov xs θ k) := by
  have : Nonempty (Fin N) := ⟨⟨0, hx.pos⟩⟩
  exact sum_mul_log_multivariateGaussianPDFReal_le (fun n => resp_pos θ (xs n) k) hx.spans μ hS

/-- **The weight update maximizes the weights term**: over all mixing weights,
`∑ k, N k log π k` is largest at `π k = N k / N` (Gibbs' inequality). -/
theorem sum_mass_mul_log_le (hN0 : 0 < N) (θ : ValidParams d K) {w : Fin K → ℝ}
    (hw : ∀ k, 0 < w k) (hsum : ∑ k, w k = 1) :
    ∑ k, mass xs θ k * log (w k) ≤ ∑ k, mass xs θ k * log (mass xs θ k / N) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast hN0
  have hq : IsDist fun k => mass xs θ k / N :=
    ⟨fun k => (div_pos (mass_pos xs hN0 θ k) hN).le, by
      rw [← Finset.sum_div, sum_mass, div_self hN.ne']⟩
  have h := sum_mul_log_sub_le hw hq
  rw [hsum, log_one] at h
  have heq : ∑ k, mass xs θ k * log (w k) - ∑ k, mass xs θ k * log (mass xs θ k / N) =
      N * ∑ k, mass xs θ k / N * (log (w k) - log (mass xs θ k / N)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  have : N * ∑ k, mass xs θ k / N * (log (w k) - log (mass xs θ k / N)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hN.le h
  linarith

/-- **The M-step maximizes `Q(· | θ)`**: no valid parameter `θ'` has a larger `Q(θ' | θ)` than the
EM update `emStep xs hx θ`. -/
theorem emQ_le_emStep (hx : SpansAffinely xs) (θ' θ : ValidParams d K) :
    emQ joint xs θ' θ ≤ emQ joint xs (emStep xs hx θ) θ := by
  rw [emQ_eq, emQ_eq, Finset.sum_add_distrib, Finset.sum_add_distrib]
  exact add_le_add (sum_mass_mul_log_le xs hx.pos θ θ'.2.weight_pos θ'.2.weight_sum)
    (Finset.sum_le_sum fun k _ => compTerm_le hx θ k _ (θ'.2.cov_posDef k))

/-- **Each EM step for the full-covariance Gaussian mixture does not decrease the
log-likelihood** (from the EM theorem `logLik_le_of_emQ_le`). -/
theorem logLik_le_emStep (hx : SpansAffinely xs) (θ : ValidParams d K) :
    logLik joint xs θ ≤ logLik joint xs (emStep xs hx θ) := by
  have := nonempty_of_valid θ
  exact logLik_le_of_emQ_le (fun θ x k => joint_pos θ x k) xs (emQ_le_emStep xs hx θ θ)

/-- **The log-likelihood is monotone along the EM iterates** of the full-covariance Gaussian
mixture. -/
theorem logLik_iterate_emStep_monotone (hx : SpansAffinely xs) (θ₀ : ValidParams d K) :
    Monotone fun t => logLik joint xs ((emStep xs hx)^[t] θ₀) := by
  have := nonempty_of_valid θ₀
  exact logLik_iterate_monotone (fun θ x k => joint_pos θ x k) xs
    (fun θ => emQ_le_emStep xs hx θ θ) θ₀

end Cslib.MachineLearning.LatentVariable.GaussianMixtureFullCov
