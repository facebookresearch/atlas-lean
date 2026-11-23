/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.Basic
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import MathlibExt.Probability.Statistics.PoissonLikelihood
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Canonical logistic and Poisson generalized linear models

The logistic (Bernoulli, logit link) and Poisson (log link) models are instances of the generic
canonical-link GLM of `GLM.Basic`: `logisticCumulant` and `poissonCumulant` are
`CanonicalCumulant`s on the natural-parameter domain `Θ = ℝ`, with

* Bernoulli: cumulant `b θ = log (1 + exp θ)`, mean `σ θ` (Mathlib's `Real.sigmoid`), variance
  `σ θ (1 - σ θ)`;
* Poisson: cumulant, mean and variance all `exp`.

Observations are indexed by a finite type `ι`, coefficients by a finite type `κ`; the linear
predictor is `GLM.glmPredictor X o β = X β + o` with a fixed offset `o`. Both objectives are the
generic `CanonicalCumulant.glmLogLik` at unit dispersion (`unitDispersion`), so the score,
Hessian, concavity and uniqueness results of `GLM.Basic` apply to them directly; this file only
specializes them. The responses `y` are fixed observed values (real for the logistic objective and
the Poisson kernel, natural counts for the Poisson likelihood).

* **Bernoulli with logit link.** `logisticLogLik = logisticCumulant.glmLogLik unitDispersion`;
  explicitly `ℓ(β) = ∑ᵢ (yᵢ ηᵢ - log (1 + exp ηᵢ))` (`logisticLogLik_eq_sum`).
  `sigmoid_logLik_term` is the per-observation identity
  `y log σ(η) + (1 - y) log (1 - σ(η)) = y η - log (1 + exp η)`, valid for every real `y`.
* **Poisson with log link.** The kernel `poissonLogLikKernel = poissonCumulant.glmLogLik
  unitDispersion` is `∑ᵢ (yᵢ ηᵢ - exp ηᵢ)` for every real `y` (`poissonLogLikKernel_eq_sum`).
  For counts `y : ι → ℕ` the log likelihood `poissonLogLik` is the shared count likelihood
  `PoissonLikelihood.poissonLogLik` at the means `exp ηᵢ`; for independent
  `Yᵢ ~ Poisson(exp ηᵢ)` it is the log-probability of the observed counts under their joint law
  (`poissonLogLik_eq_log_pi_poissonMeasure`). `poissonLogLik_eq_kernel` shows that it is the
  kernel minus the `β`-free constant `∑ᵢ log yᵢ!`, and `isMaxOn_poissonLogLik_iff` that both have
  the same maximizers.

## Exponential-family structure

The cumulants are the log-partition functions of the response families, with sufficient statistic
`T(y) = y`:

* Bernoulli: `logisticCumulant_cumulant_eq_log_sum_exp` gives
  `b θ = log ∑_{y ∈ {0, 1}} exp (y θ)`, and `exp_logisticCumulant_one`,
  `exp_logisticCumulant_zero` that `exp (y θ - b θ)` is `σ θ` at `y = 1` and `1 - σ θ` at
  `y = 0`, i.e. the Bernoulli probabilities with success probability `σ θ`.
* Poisson: `poissonMeasure_real_singleton_eq_exp` gives
  `P(Y = k) = exp (k θ - b θ) / k!` for `Y ~ Poisson(exp θ)`.

## Main results

For both models (the Poisson statements are about the kernel `poissonLogLikKernel`):

* `logisticCumulant_glmScore`, `poissonCumulant_glmScore`: the generic score is `Xᵀ (y - μ(β))`;
  `logisticCumulant_glmHessian`, `poissonCumulant_glmHessian`: the generic Hessian is `-Xᵀ W X`
  with `Wᵢ = σ(ηᵢ)(1 - σ(ηᵢ))`, resp. `Wᵢ = exp ηᵢ`.
* `hasFDerivAt_logisticLogLik`, `hasFDerivAt_poissonLogLikKernel`: the Fréchet derivative at `β` is
  `Real.dotL (Xᵀ (y - μ(β)))`, and the `hasGradientAt_*` corollaries state that `Xᵀ (y - μ(β))` is
  the gradient on `EuclideanSpace ℝ κ`. `hasFDerivAt_logisticScore`,
  `hasFDerivAt_poissonScore`: the derivative of the score is the Hessian.
* `deriv2_logisticLogLik_line`, `deriv2_poissonLogLikKernel_line`: along `t ↦ β + t u` the second
  derivative at `0` is `-∑ᵢ wᵢ ((X u)ᵢ)²`.
* `concaveOn_logisticLogLik`, `concaveOn_poissonLogLikKernel`: concavity on all of `κ → ℝ`.
* `logisticLogLik_maximizer_unique`, `poissonLogLikKernel_maximizer_unique`: if `β ↦ X β` is
  injective there is at most one maximizer. Existence is not claimed and can fail:
  `logisticLogLik_separation_not_isMaxOn` (complete separation) and
  `poissonLogLikKernel_allZero_not_isMaxOn` (all-zero counts) have no maximizer, the first with an
  injective design (`separationDesign_mulVec_injective`).
* `logisticDeviance` and `logisticDeviance_nonneg` for binary responses. Outside the response
  domain `[0, 1]` the saturated likelihood `logisticLogLikSaturated` and the deviance are
  algebraic extensions without a likelihood or deviance meaning.

## Response laws

The models are normalized: `σ(η) ∈ (0, 1)` (`unitInterval.sigmoid η`), so the Bernoulli response
law is `ProbabilityTheory.bernoulliMeasure 1 0 (unitInterval.sigmoid η)`, and the Poisson law is
`ProbabilityTheory.poissonMeasure ⟨exp η, (exp_pos η).le⟩`. By
`poissonLogLik_eq_log_pi_poissonMeasure`, `poissonLogLik` is the log-probability of the observed
counts under the product (`MeasureTheory.Measure.pi`) of these Poisson laws, the joint law of
independent responses.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.GLM

open Finset Real Matrix

/-- The unit dispersion `φ = 1`. -/
def unitDispersion : Dispersion := ⟨1, one_pos⟩

@[simp]
theorem coe_unitDispersion : (unitDispersion : ℝ) = 1 := rfl

/-! ### A second derivative along a line -/

/-- On a natural-parameter domain equal to `ℝ`, the second derivative of the log likelihood along
`t ↦ β + t u` at `0` is the Hessian quadratic form `uᵀ H(β) u`. -/
private lemma deriv2_glmLogLik_line {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (F : CanonicalCumulant) (hF : F.natDomain = Set.univ) (φ : Dispersion)
    (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β u : κ → ℝ) :
    deriv^[2] (fun t : ℝ => F.glmLogLik φ X o y (β + t • u)) 0 =
      u ⬝ᵥ (F.glmHessian φ X o β *ᵥ u) := by
  have hmem : ∀ γ, γ ∈ F.glmDomain X o := fun γ i => hF ▸ Set.mem_univ _
  have hl : ∀ t : ℝ, HasDerivAt (fun t : ℝ => β + t • u) u t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const u).const_add β
  have hd : deriv (fun t : ℝ => F.glmLogLik φ X o y (β + t • u)) =
      fun t => F.glmScore φ X o y (β + t • u) ⬝ᵥ u := by
    funext t
    have h := (F.hasFDerivAt_glmLogLik φ X o y (hmem (β + t • u))).comp_hasDerivAt t (hl t)
    rw [Function.comp_def] at h
    rw [h.deriv, Real.dotL_apply, dotProduct_comm]
  have hs := (F.hasFDerivAt_glmScore φ X o y (hmem β)).comp_hasDerivAt_of_eq 0 (hl 0)
    (by simp)
  have h2 := (Real.hasFDerivAt_dotProduct u _).comp_hasDerivAt 0 hs
  rw [Function.comp_def, Function.comp_def] at h2
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, Real.dotL_apply] at h2
  rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply, hd, h2.deriv,
    dotProduct_comm]

variable {ι κ : Type*} [Fintype κ]

/-! ### The Bernoulli cumulant -/

private lemma sigmoid_eq_exp_div (η : ℝ) : sigmoid η = exp η / (1 + exp η) := by
  rw [sigmoid_def, exp_neg]
  field_simp
  ring

/-- The derivative of the Bernoulli cumulant `log (1 + exp x)` is `σ x`. -/
theorem hasDerivAt_log_one_add_exp (x : ℝ) :
    HasDerivAt (fun x => log (1 + exp x)) (sigmoid x) x := by
  have h := ((hasDerivAt_exp x).const_add 1).log (by positivity)
  convert h using 1
  rw [sigmoid_eq_exp_div]

/-- The Bernoulli variance `σ θ (1 - σ θ)` is strictly positive. -/
theorem sigmoid_mul_one_sub_pos (θ : ℝ) : 0 < sigmoid θ * (1 - sigmoid θ) :=
  mul_pos (sigmoid_pos θ) (sub_pos.2 (sigmoid_lt_one θ))

/-- The canonical Bernoulli (logit-link) cumulant on `Θ = ℝ`: `b θ = log (1 + exp θ)`, mean
`σ θ`, variance `σ θ (1 - σ θ)`. -/
noncomputable def logisticCumulant : CanonicalCumulant where
  natDomain := Set.univ
  isOpen_natDomain := isOpen_univ
  convex_natDomain := convex_univ
  cumulant θ := log (1 + exp θ)
  mean := sigmoid
  variance θ := sigmoid θ * (1 - sigmoid θ)
  hasDerivAt_cumulant θ _ := hasDerivAt_log_one_add_exp θ
  hasDerivAt_mean θ _ := hasDerivAt_sigmoid θ
  variance_nonneg θ _ := (sigmoid_mul_one_sub_pos θ).le

@[simp] theorem logisticCumulant_natDomain : logisticCumulant.natDomain = Set.univ := rfl

@[simp] theorem logisticCumulant_cumulant (θ : ℝ) :
    logisticCumulant.cumulant θ = log (1 + exp θ) := rfl

@[simp] theorem logisticCumulant_mean : logisticCumulant.mean = sigmoid := rfl

@[simp] theorem logisticCumulant_variance (θ : ℝ) :
    logisticCumulant.variance θ = sigmoid θ * (1 - sigmoid θ) := rfl

theorem logisticCumulant_mem_glmDomain (X : Matrix ι κ ℝ) (o : ι → ℝ) (β : κ → ℝ) :
    β ∈ logisticCumulant.glmDomain X o := fun _ => Set.mem_univ _

@[simp] theorem logisticCumulant_glmDomain (X : Matrix ι κ ℝ) (o : ι → ℝ) :
    logisticCumulant.glmDomain X o = Set.univ :=
  Set.eq_univ_of_forall (logisticCumulant_mem_glmDomain X o)

/-! ### Bernoulli exponential-family structure -/

/-- **The Bernoulli log-partition function.** With sufficient statistic `T(y) = y` and counting
measure on `{0, 1}`, the cumulant is `b θ = log ∑_{y ∈ {0, 1}} exp (y θ)`. -/
theorem logisticCumulant_cumulant_eq_log_sum_exp (θ : ℝ) :
    logisticCumulant.cumulant θ = log (∑ y ∈ ({0, 1} : Finset ℝ), exp (y * θ)) := by
  rw [Finset.sum_pair zero_ne_one]
  simp

/-- The Bernoulli density `exp (y θ - b θ)` at `y = 1` is the success probability `σ θ`. -/
theorem exp_logisticCumulant_one (θ : ℝ) :
    exp (1 * θ - logisticCumulant.cumulant θ) = sigmoid θ := by
  rw [logisticCumulant_cumulant, one_mul, exp_sub, exp_log (by positivity), sigmoid_eq_exp_div]

/-- The Bernoulli density `exp (y θ - b θ)` at `y = 0` is the failure probability `1 - σ θ`. -/
theorem exp_logisticCumulant_zero (θ : ℝ) :
    exp (0 * θ - logisticCumulant.cumulant θ) = 1 - sigmoid θ := by
  have h : 0 < 1 + exp θ := by positivity
  rw [logisticCumulant_cumulant, zero_mul, zero_sub, exp_neg, exp_log h, sigmoid_eq_exp_div]
  field_simp
  ring

/-! ### The Poisson cumulant -/

/-- The canonical Poisson (log-link) cumulant on `Θ = ℝ`: cumulant, mean and variance are all
`exp`. -/
noncomputable def poissonCumulant : CanonicalCumulant where
  natDomain := Set.univ
  isOpen_natDomain := isOpen_univ
  convex_natDomain := convex_univ
  cumulant := exp
  mean := exp
  variance := exp
  hasDerivAt_cumulant θ _ := hasDerivAt_exp θ
  hasDerivAt_mean θ _ := hasDerivAt_exp θ
  variance_nonneg θ _ := (exp_pos θ).le

@[simp] theorem poissonCumulant_natDomain : poissonCumulant.natDomain = Set.univ := rfl

@[simp] theorem poissonCumulant_cumulant : poissonCumulant.cumulant = exp := rfl

@[simp] theorem poissonCumulant_mean : poissonCumulant.mean = exp := rfl

@[simp] theorem poissonCumulant_variance : poissonCumulant.variance = exp := rfl

theorem poissonCumulant_mem_glmDomain (X : Matrix ι κ ℝ) (o : ι → ℝ) (β : κ → ℝ) :
    β ∈ poissonCumulant.glmDomain X o := fun _ => Set.mem_univ _

@[simp] theorem poissonCumulant_glmDomain (X : Matrix ι κ ℝ) (o : ι → ℝ) :
    poissonCumulant.glmDomain X o = Set.univ :=
  Set.eq_univ_of_forall (poissonCumulant_mem_glmDomain X o)

/-- **The Poisson exponential-family density.** For `Y ~ Poisson(exp θ)`,
`P(Y = k) = exp (k θ - b θ) / k!`: sufficient statistic `T(k) = k`, log-partition function
`b = exp`, base measure `1 / k!` on `ℕ`. -/
theorem poissonMeasure_real_singleton_eq_exp (θ : ℝ) (k : ℕ) :
    (ProbabilityTheory.poissonMeasure ⟨exp θ, (exp_pos θ).le⟩).real {k} =
      exp (k * θ - poissonCumulant.cumulant θ) / k.factorial := by
  refine (ProbabilityTheory.poissonMeasure_real_singleton _ k).trans ?_
  change exp (-exp θ) * exp θ ^ k / k.factorial = _
  rw [poissonCumulant_cumulant, ← exp_nat_mul, ← exp_add, neg_add_eq_sub]

variable [Fintype ι]

/-! ### The Bernoulli model with logit link -/

/-- The per-observation Bernoulli log likelihood in canonical form, for every real `y`:
`y log σ(η) + (1 - y) log (1 - σ(η)) = y η - log (1 + exp η)`. -/
theorem sigmoid_logLik_term (y η : ℝ) :
    y * log (sigmoid η) + (1 - y) * log (1 - sigmoid η) = y * η - log (1 + exp η) := by
  have h1 : 0 < 1 + exp η := by positivity
  have hs' : 1 - sigmoid η = 1 / (1 + exp η) := by
    rw [sigmoid_eq_exp_div]
    field_simp
    ring
  rw [hs', sigmoid_eq_exp_div, log_div (exp_pos η).ne' h1.ne', log_exp, one_div, log_inv]
  ring

/-- The log likelihood of the canonical Bernoulli (logistic regression) model: the generic
canonical-link log likelihood of `logisticCumulant` at unit dispersion, explicitly
`ℓ(β) = ∑ᵢ (yᵢ ηᵢ(β) - log (1 + exp ηᵢ(β)))` (`logisticLogLik_eq_sum`). For `yᵢ ∈ {0, 1}` each
term is `log P(Yᵢ = yᵢ)` under success probability `σ(ηᵢ)` (`sigmoid_logLik_term`). -/
noncomputable def logisticLogLik (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) : ℝ :=
  logisticCumulant.glmLogLik unitDispersion X o y β

theorem logisticLogLik_eq_sum (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) :
    logisticLogLik X o y β =
      ∑ i, (y i * glmPredictor X o β i - log (1 + exp (glmPredictor X o β i))) := by
  simp [logisticLogLik, CanonicalCumulant.glmLogLik]

/-- The generic score of `logisticCumulant` at unit dispersion is `Xᵀ (y - σ(η(β)))`. -/
theorem logisticCumulant_glmScore (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) :
    logisticCumulant.glmScore unitDispersion X o y β =
      X.transpose *ᵥ (y - sigmoid ∘ glmPredictor X o β) := by
  simp only [CanonicalCumulant.glmScore, coe_unitDispersion, inv_one, one_smul,
    logisticCumulant_mean]
  rfl

/-- The generic Hessian of `logisticCumulant` at unit dispersion is `-Xᵀ W X` with Bernoulli
weights `Wᵢ = σ(ηᵢ)(1 - σ(ηᵢ))`. -/
theorem logisticCumulant_glmHessian [DecidableEq ι] [DecidableEq κ] (X : Matrix ι κ ℝ)
    (o : ι → ℝ) (β : κ → ℝ) :
    logisticCumulant.glmHessian unitDispersion X o β =
      -IRLS.weightedGram X
        (fun i => sigmoid (glmPredictor X o β i) * (1 - sigmoid (glmPredictor X o β i))) := by
  simp only [CanonicalCumulant.glmHessian, coe_unitDispersion, inv_one, one_smul]
  rfl

/-- **The logistic score.** The Fréchet derivative of the logistic log likelihood at `β` is
`v ↦ ⟪v, Xᵀ (y - σ(η(β)))⟫`. -/
theorem hasFDerivAt_logisticLogLik (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) :
    HasFDerivAt (logisticLogLik X o y)
      (Real.dotL (X.transpose *ᵥ (y - sigmoid ∘ glmPredictor X o β))) β := by
  rw [← logisticCumulant_glmScore]
  exact logisticCumulant.hasFDerivAt_glmLogLik unitDispersion X o y
    (logisticCumulant_mem_glmDomain X o β)

/-- The logistic score `Xᵀ (y - σ(η(β)))` is the gradient of the log likelihood on
`EuclideanSpace ℝ κ`. -/
theorem hasGradientAt_logisticLogLik (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) :
    HasGradientAt (fun b : EuclideanSpace ℝ κ => logisticLogLik X o y b.ofLp)
      (WithLp.toLp 2 (X.transpose *ᵥ (y - sigmoid ∘ glmPredictor X o β))) (WithLp.toLp 2 β) :=
  Real.hasGradientAt_ofLp (hasFDerivAt_logisticLogLik X o y β)

/-- **The logistic Hessian.** The derivative of the logistic score `Xᵀ (y - σ(η(β)))` at `β` is
`-Xᵀ W X` with `Wᵢ = σ(ηᵢ)(1 - σ(ηᵢ))`. -/
theorem hasFDerivAt_logisticScore [DecidableEq ι] [DecidableEq κ] (X : Matrix ι κ ℝ)
    (o y : ι → ℝ) (β : κ → ℝ) :
    HasFDerivAt (fun β => X.transpose *ᵥ (y - sigmoid ∘ glmPredictor X o β))
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (-IRLS.weightedGram X
        (fun i => sigmoid (glmPredictor X o β i) * (1 - sigmoid (glmPredictor X o β i)))))) β := by
  rw [← logisticCumulant_glmHessian]
  simp only [← logisticCumulant_glmScore]
  exact logisticCumulant.hasFDerivAt_glmScore unitDispersion X o y
    (logisticCumulant_mem_glmDomain X o β)

/-- **The logistic Hessian quadratic form.** Along `t ↦ β + t u` the second derivative at `0` is
`-∑ᵢ σ(ηᵢ)(1 - σ(ηᵢ)) ((X u)ᵢ)²`. -/
theorem deriv2_logisticLogLik_line (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β u : κ → ℝ) :
    deriv^[2] (fun t : ℝ => logisticLogLik X o y (β + t • u)) 0 =
      -∑ i, sigmoid (glmPredictor X o β i) * (1 - sigmoid (glmPredictor X o β i)) *
        (X *ᵥ u) i ^ 2 := by
  classical
  refine (deriv2_glmLogLik_line logisticCumulant rfl unitDispersion X o y β u).trans ?_
  rw [CanonicalCumulant.dotProduct_glmHessian_mulVec]
  simp [CanonicalCumulant.glmWeights]

/-- The logistic log likelihood is concave on `κ → ℝ`. -/
theorem concaveOn_logisticLogLik (X : Matrix ι κ ℝ) (o y : ι → ℝ) :
    ConcaveOn ℝ Set.univ (logisticLogLik X o y) := by
  have h := logisticCumulant.concaveOn_glmLogLik unitDispersion X o y
  rw [logisticCumulant_glmDomain] at h
  exact h

/-- **At most one logistic maximum likelihood estimate.** If `β ↦ X β` is injective (full column
rank), the logistic log likelihood has at most one maximizer. The weights `σ(1 - σ)` are always
positive, so every term is strictly concave in its linear predictor. -/
theorem logisticLogLik_maximizer_unique (X : Matrix ι κ ℝ) (o y : ι → ℝ)
    (hX : Function.Injective X.mulVec) {β₁ β₂ : κ → ℝ}
    (h₁ : IsMaxOn (logisticLogLik X o y) Set.univ β₁)
    (h₂ : IsMaxOn (logisticLogLik X o y) Set.univ β₂) : β₁ = β₂ :=
  logisticCumulant.glmLogLik_maximizer_unique unitDispersion hX
    (fun θ _ => sigmoid_mul_one_sub_pos θ) o y (logisticCumulant_mem_glmDomain X o β₁)
    (logisticCumulant_mem_glmDomain X o β₂)
    (by rw [logisticCumulant_glmDomain]; exact h₁) (by rw [logisticCumulant_glmDomain]; exact h₂)

private lemma log_one_add_exp (x : ℝ) : log (1 + exp x) = x + log (1 + exp (-x)) := by
  have e : 1 + exp x = exp x * (1 + exp (-x)) := by
    rw [mul_add, mul_one, ← exp_add, add_neg_cancel, exp_zero, add_comm]
  rw [e, log_mul (exp_pos x).ne' (by positivity), log_exp]

/-- Each binary logistic term is negative: `y η < log (1 + exp η)` for `y ∈ {0, 1}`. -/
theorem logisticTerm_neg {y : ℝ} (hy : y = 0 ∨ y = 1) (η : ℝ) :
    y * η - log (1 + exp η) < 0 := by
  have hpos : ∀ x : ℝ, 0 < log (1 + exp x) := fun x =>
    log_pos (by linarith [exp_pos x])
  rcases hy with rfl | rfl
  · linarith [hpos η]
  · rw [log_one_add_exp]
    linarith [hpos (-η)]

/-- For binary responses the logistic log likelihood is nonpositive. -/
theorem logisticLogLik_nonpos (X : Matrix ι κ ℝ) (o y : ι → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (β : κ → ℝ) : logisticLogLik X o y β ≤ 0 := by
  rw [logisticLogLik_eq_sum]
  exact Finset.sum_nonpos fun i _ => (logisticTerm_neg (hy i) _).le

/-! ### Complete separation: no logistic maximizer -/

/-- The single-covariate design `x = (-1, 1)` without intercept. -/
def separationDesign : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of ![![-1], ![1]]

/-- The separation design has full column rank: `β ↦ X β` is injective. -/
theorem separationDesign_mulVec_injective : Function.Injective separationDesign.mulVec := by
  intro β γ h
  have h1 := congrFun h 1
  simp only [separationDesign, Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.of_apply,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul] at h1
  funext k
  rw [Subsingleton.elim k 0]
  exact h1

/-- Under complete separation (`x = (-1, 1)`, `y = (0, 1)`, no offset) the logistic log likelihood
is `-2 log (1 + exp (-β))`. -/
theorem logisticLogLik_separation (β : Fin 1 → ℝ) :
    logisticLogLik separationDesign 0 ![0, 1] β = -2 * log (1 + exp (-β 0)) := by
  simp only [logisticLogLik_eq_sum, glmPredictor_apply, separationDesign, Matrix.mulVec,
    dotProduct, Fin.sum_univ_one, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply, add_zero, zero_mul, one_mul,
    neg_mul, zero_sub]
  rw [log_one_add_exp (β 0)]
  ring

/-- Under complete separation the logistic log likelihood is negative everywhere. -/
theorem logisticLogLik_separation_neg (β : Fin 1 → ℝ) :
    logisticLogLik separationDesign 0 ![0, 1] β < 0 := by
  rw [logisticLogLik_separation]
  have : 0 < log (1 + exp (-β 0)) := log_pos (by linarith [exp_pos (-β 0)])
  linarith

/-- Under complete separation every coefficient is beaten by a larger one. -/
theorem logisticLogLik_separation_lt (β : Fin 1 → ℝ) :
    logisticLogLik separationDesign 0 ![0, 1] β <
      logisticLogLik separationDesign 0 ![0, 1] (β + 1) := by
  rw [logisticLogLik_separation, logisticLogLik_separation]
  have : exp (-(β + 1) 0) < exp (-β 0) := exp_lt_exp.2 (by simp)
  have := log_lt_log (by positivity) (by linarith : 1 + exp (-(β + 1) 0) < 1 + exp (-β 0))
  linarith

/-- **Separation: no logistic maximum likelihood estimate**, although the design has full column
rank (`separationDesign_mulVec_injective`), so a maximizer would be unique. -/
theorem logisticLogLik_separation_not_isMaxOn (β : Fin 1 → ℝ) :
    ¬ IsMaxOn (logisticLogLik separationDesign 0 ![0, 1]) Set.univ β := fun h =>
  (logisticLogLik_separation_lt β).not_ge (h (Set.mem_univ (β + 1)))

/-! ### Deviance -/

/-- The saturated Bernoulli log likelihood `∑ᵢ (yᵢ log yᵢ + (1 - yᵢ) log (1 - yᵢ)) = -∑ᵢ H(yᵢ)`
with `H = Real.binEntropy`; it is `0` for binary responses. Its likelihood interpretation applies
only on the response domain `[0, 1]`: for other real `y` the formula is an algebraic extension,
not a log probability (with Lean's `log (-1) = 0`, the single response `y = 2` gives
`2 log 2 > 0`). -/
noncomputable def logisticLogLikSaturated (y : ι → ℝ) : ℝ :=
  -∑ i, binEntropy (y i)

theorem logisticLogLikSaturated_eq (y : ι → ℝ) :
    logisticLogLikSaturated y = ∑ i, (y i * log (y i) + (1 - y i) * log (1 - y i)) := by
  simp only [logisticLogLikSaturated, binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    negMulLog, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem logisticLogLikSaturated_eq_zero (y : ι → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1) :
    logisticLogLikSaturated y = 0 := by
  simp only [logisticLogLikSaturated, neg_eq_zero]
  exact Finset.sum_eq_zero fun i _ => by rcases hy i with h | h <;> simp [h]

/-- The logistic deviance `2 (ℓ_sat - ℓ(β))`, with `ℓ = logisticLogLik` the generic
canonical-link log likelihood of `logisticCumulant`. Its deviance interpretation applies only on
the response domain `[0, 1]`; for binary responses it is `-2 ℓ(β) ≥ 0` (`logisticDeviance_eq`,
`logisticDeviance_nonneg`). For other real `y` it is an algebraic extension and can be negative
(`y = 2` and `η = log 7` give `10 log 2 - 4 log 7 < 0`). -/
noncomputable def logisticDeviance (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) : ℝ :=
  2 * (logisticLogLikSaturated y - logisticLogLik X o y β)

/-- For binary responses the deviance is `-2 ℓ(β)`. -/
theorem logisticDeviance_eq (X : Matrix ι κ ℝ) (o y : ι → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (β : κ → ℝ) : logisticDeviance X o y β = -2 * logisticLogLik X o y β := by
  rw [logisticDeviance, logisticLogLikSaturated_eq_zero y hy]
  ring

/-- For binary responses the deviance is nonnegative. -/
theorem logisticDeviance_nonneg (X : Matrix ι κ ℝ) (o y : ι → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (β : κ → ℝ) : 0 ≤ logisticDeviance X o y β := by
  rw [logisticDeviance_eq X o y hy]
  linarith [logisticLogLik_nonpos X o y hy β]

/-! ### The Poisson model with log link -/

/-- The algebraic kernel of the canonical Poisson (log-linear) log likelihood: the generic
canonical-link log likelihood of `poissonCumulant` at unit dispersion, explicitly
`∑ᵢ (yᵢ ηᵢ(β) - exp ηᵢ(β))` (`poissonLogLikKernel_eq_sum`), defined for every real response
vector `y`. It is a likelihood only up to a constant and only for counts: for `y : ι → ℕ` it
exceeds `poissonLogLik` by the `β`-free term `∑ᵢ log yᵢ!` (`poissonLogLik_eq_kernel`). -/
noncomputable def poissonLogLikKernel (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) : ℝ :=
  poissonCumulant.glmLogLik unitDispersion X o y β

theorem poissonLogLikKernel_eq_sum (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) :
    poissonLogLikKernel X o y β =
      ∑ i, (y i * glmPredictor X o β i - exp (glmPredictor X o β i)) := by
  simp [poissonLogLikKernel, CanonicalCumulant.glmLogLik]

/-- **The canonical Poisson log likelihood of counts.** For natural-valued counts `y : ι → ℕ`
this is the shared Poisson count log-likelihood
`MathlibExt.Probability.Statistics.PoissonLikelihood.poissonLogLik` at the means `exp ηᵢ(β)`.
For independent responses `Yᵢ ~ Poisson(exp ηᵢ(β))` (`ProbabilityTheory.poissonMeasure`) it is
the log-probability of the observed counts `y` under their joint law
(`poissonLogLik_eq_log_pi_poissonMeasure`). -/
noncomputable def poissonLogLik (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ) (β : κ → ℝ) : ℝ :=
  PoissonLikelihood.poissonLogLik (fun i => exp (glmPredictor X o β i)) y

/-- **The joint law of independent Poisson responses.** For independent responses
`Yᵢ ~ Poisson(exp ηᵢ(β))`, the canonical Poisson log likelihood of the counts `y` is the
log-probability of `y` under their joint law, by
`PoissonLikelihood.log_pi_poissonMeasure_real_singleton`. -/
theorem poissonLogLik_eq_log_pi_poissonMeasure (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ)
    (β : κ → ℝ) :
    poissonLogLik X o y β =
      log ((MeasureTheory.Measure.pi fun i => ProbabilityTheory.poissonMeasure
        ⟨exp (glmPredictor X o β i), (exp_pos _).le⟩).real {y}) :=
  (PoissonLikelihood.log_pi_poissonMeasure_real_singleton
    (fun i => ⟨exp (glmPredictor X o β i), (exp_pos _).le⟩)
    (fun i => NNReal.coe_pos.mp (exp_pos (glmPredictor X o β i))) y).symm

/-- **The Poisson likelihood of counts is the kernel minus a `β`-free constant:**
`ℓ(β) = ∑ᵢ (yᵢ ηᵢ(β) - exp ηᵢ(β)) - ∑ᵢ log yᵢ!`. -/
theorem poissonLogLik_eq_kernel (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ) (β : κ → ℝ) :
    poissonLogLik X o y β =
      poissonLogLikKernel X o (fun i => (y i : ℝ)) β - ∑ i, log ((y i).factorial : ℝ) := by
  rw [poissonLogLikKernel_eq_sum]
  simp only [poissonLogLik, PoissonLikelihood.poissonLogLik, log_exp, ← Finset.sum_sub_distrib]

/-- The Poisson likelihood of counts and its kernel have the same maximizers on every set, so
`poissonLogLikKernel_maximizer_unique` and `poissonLogLikKernel_allZero_not_isMaxOn` apply to
`poissonLogLik`. -/
theorem isMaxOn_poissonLogLik_iff (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ) {s : Set (κ → ℝ)}
    {β : κ → ℝ} :
    IsMaxOn (poissonLogLik X o y) s β ↔
      IsMaxOn (poissonLogLikKernel X o (fun i => (y i : ℝ))) s β := by
  simp only [isMaxOn_iff, poissonLogLik_eq_kernel, sub_le_sub_iff_right]

/-- The generic score of `poissonCumulant` at unit dispersion is `Xᵀ (y - exp (η(β)))`. -/
theorem poissonCumulant_glmScore (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) :
    poissonCumulant.glmScore unitDispersion X o y β =
      X.transpose *ᵥ (y - exp ∘ glmPredictor X o β) := by
  simp only [CanonicalCumulant.glmScore, coe_unitDispersion, inv_one, one_smul,
    poissonCumulant_mean]
  rfl

/-- The generic Hessian of `poissonCumulant` at unit dispersion is `-Xᵀ W X` with Poisson
weights `Wᵢ = exp ηᵢ`. -/
theorem poissonCumulant_glmHessian [DecidableEq ι] [DecidableEq κ] (X : Matrix ι κ ℝ)
    (o : ι → ℝ) (β : κ → ℝ) :
    poissonCumulant.glmHessian unitDispersion X o β =
      -IRLS.weightedGram X (fun i => exp (glmPredictor X o β i)) := by
  simp only [CanonicalCumulant.glmHessian, coe_unitDispersion, inv_one, one_smul]
  rfl

/-- **The Poisson score.** The Fréchet derivative of the Poisson kernel at `β` is
`v ↦ ⟪v, Xᵀ (y - exp (η(β)))⟫`. -/
theorem hasFDerivAt_poissonLogLikKernel (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) :
    HasFDerivAt (poissonLogLikKernel X o y)
      (Real.dotL (X.transpose *ᵥ (y - exp ∘ glmPredictor X o β))) β := by
  rw [← poissonCumulant_glmScore]
  exact poissonCumulant.hasFDerivAt_glmLogLik unitDispersion X o y
    (poissonCumulant_mem_glmDomain X o β)

/-- The Poisson score `Xᵀ (y - exp (η(β)))` is the gradient of the Poisson kernel on
`EuclideanSpace ℝ κ`. -/
theorem hasGradientAt_poissonLogLikKernel (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) :
    HasGradientAt (fun b : EuclideanSpace ℝ κ => poissonLogLikKernel X o y b.ofLp)
      (WithLp.toLp 2 (X.transpose *ᵥ (y - exp ∘ glmPredictor X o β))) (WithLp.toLp 2 β) :=
  Real.hasGradientAt_ofLp (hasFDerivAt_poissonLogLikKernel X o y β)

/-- **The Poisson Hessian.** The derivative of the Poisson score `Xᵀ (y - exp (η(β)))` at `β` is
`-Xᵀ W X` with `Wᵢ = exp ηᵢ`. -/
theorem hasFDerivAt_poissonScore [DecidableEq ι] [DecidableEq κ] (X : Matrix ι κ ℝ)
    (o y : ι → ℝ) (β : κ → ℝ) :
    HasFDerivAt (fun β => X.transpose *ᵥ (y - exp ∘ glmPredictor X o β))
      (LinearMap.toContinuousLinearMap (Matrix.toLin'
        (-IRLS.weightedGram X (fun i => exp (glmPredictor X o β i))))) β := by
  rw [← poissonCumulant_glmHessian]
  simp only [← poissonCumulant_glmScore]
  exact poissonCumulant.hasFDerivAt_glmScore unitDispersion X o y
    (poissonCumulant_mem_glmDomain X o β)

/-- **The Poisson Hessian quadratic form.** Along `t ↦ β + t u` the second derivative at `0` is
`-∑ᵢ exp ηᵢ ((X u)ᵢ)²`. -/
theorem deriv2_poissonLogLikKernel_line (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β u : κ → ℝ) :
    deriv^[2] (fun t : ℝ => poissonLogLikKernel X o y (β + t • u)) 0 =
      -∑ i, exp (glmPredictor X o β i) * (X *ᵥ u) i ^ 2 := by
  classical
  refine (deriv2_glmLogLik_line poissonCumulant rfl unitDispersion X o y β u).trans ?_
  rw [CanonicalCumulant.dotProduct_glmHessian_mulVec]
  simp [CanonicalCumulant.glmWeights]

/-- The Poisson kernel is concave on `κ → ℝ`. -/
theorem concaveOn_poissonLogLikKernel (X : Matrix ι κ ℝ) (o y : ι → ℝ) :
    ConcaveOn ℝ Set.univ (poissonLogLikKernel X o y) := by
  have h := poissonCumulant.concaveOn_glmLogLik unitDispersion X o y
  rw [poissonCumulant_glmDomain] at h
  exact h

/-- **At most one maximizer of the Poisson kernel** when `β ↦ X β` is injective, hence at most
one Poisson maximum likelihood estimate for counts (`isMaxOn_poissonLogLik_iff`). -/
theorem poissonLogLikKernel_maximizer_unique (X : Matrix ι κ ℝ) (o y : ι → ℝ)
    (hX : Function.Injective X.mulVec) {β₁ β₂ : κ → ℝ}
    (h₁ : IsMaxOn (poissonLogLikKernel X o y) Set.univ β₁)
    (h₂ : IsMaxOn (poissonLogLikKernel X o y) Set.univ β₂) : β₁ = β₂ :=
  poissonCumulant.glmLogLik_maximizer_unique unitDispersion hX (fun θ _ => exp_pos θ) o y
    (poissonCumulant_mem_glmDomain X o β₁) (poissonCumulant_mem_glmDomain X o β₂)
    (by rw [poissonCumulant_glmDomain]; exact h₁) (by rw [poissonCumulant_glmDomain]; exact h₂)

/-! ### All-zero counts: no Poisson maximizer -/

/-- With all-zero counts, an intercept-only design and no offset, the Poisson kernel is
`-|ι| exp β`. -/
theorem poissonLogLikKernel_allZero (β : Fin 1 → ℝ) :
    poissonLogLikKernel (Matrix.of fun (_ : ι) (_ : Fin 1) => (1 : ℝ)) 0 0 β =
      -(Fintype.card ι * exp (β 0)) := by
  simp [poissonLogLikKernel_eq_sum, glmPredictor_apply, Matrix.mulVec, dotProduct,
    Finset.sum_neg_distrib]

/-- **All-zero counts: no maximizer of the Poisson kernel** (at least one observation), hence no
Poisson maximum likelihood estimate (`isMaxOn_poissonLogLik_iff`): lowering the intercept always
increases the kernel. -/
theorem poissonLogLikKernel_allZero_not_isMaxOn [Nonempty ι] (β : Fin 1 → ℝ) :
    ¬ IsMaxOn (poissonLogLikKernel (Matrix.of fun (_ : ι) (_ : Fin 1) => (1 : ℝ)) 0 0)
      Set.univ β := by
  intro h
  have hle := h (Set.mem_univ (β - 1))
  simp only [Set.mem_ofPred_eq, poissonLogLikKernel_allZero, Pi.sub_apply, Pi.one_apply] at hle
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have : exp (β 0 - 1) < exp (β 0) := exp_lt_exp.2 (by linarith)
  nlinarith

end MathlibExt.Probability.Statistics.GLM
