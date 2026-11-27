/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Discriminative.LogisticRegression
public import MathlibExt.Probability.Statistics.Likelihood

/-!
# Exponential families and generalized linear models

An exponential family on a finite sample space `X` has a base measure `h : X → ℝ` (nonnegative,
not identically zero), a sufficient statistic `T : X → ι → ℝ` and natural parameters
`η : ι → ℝ`. Its density is `p η x = h x * exp (η ⬝ᵥ T x - A η)`, where the log-partition function
is `A η = log ∑ x, h x * exp (η ⬝ᵥ T x)`.

## Main results

* `sum_density`, `dist`: the density is a probability distribution (a point of Mathlib's
  `Convexity.StdSimplex`).
* `convexOn_logPartition`: the log-partition function is convex.
* `hasFDerivAt_logPartition`, `hasGradientAt_logPartition`: the gradient of the log-partition
  function is the mean
  `mean η = ∑ x, p η x • T x` of the statistic (`hasDerivAt_logPartition_line` for directional
  derivatives).
* `logPartition_sub_ge`: the supporting-hyperplane inequality
  `A η' - A η ≥ (η' - η) ⬝ᵥ mean η` (Jensen's inequality for `exp`).
* `likelihood_le_of_mean_eq`: **moment matching**: if `m • mean η★ = ∑ k, T (x k)`, then `η★`
  maximizes the likelihood of the `m` observations. For `m > 0` this says the model mean equals
  the sample mean of the statistic; for `m = 0` the likelihood is the empty product `1` and all
  parameters tie. `densityFamily`,
  `iidLikelihood_eq` and `isMaxOn_iidLikelihood_of_mean_eq` state this in the iid-likelihood
  interface of `MathlibExt/Probability/Statistics/Likelihood.lean` (counting measure).
* `logPartition_bernoulli`, `mean_bernoulli`, `dist_bernoulli`: for the Bernoulli family
  (`X = Bool`, `T b = b`) the log-partition function is the softplus, the mean is the logistic
  function, and the distribution is `bernoulliDist (sigmoid η)`, the logistic regression model.

Generalized linear models with canonical link: `glmLoss A X Y θ = ∑ k, (A (θ ⬝ᵥ X k) -
Y k * (θ ⬝ᵥ X k))`. When `A` is the log-partition function of a one-parameter exponential family
and the responses `Y k` lie in its support, this is the negative log-likelihood of the responses
with natural parameters `θ ⬝ᵥ X k`, up to terms not depending on `θ`.

* `convexOn_glmLoss`, `hasFDerivAt_glmLoss`, `hasGradientAt_glmLoss`: it is convex, with gradient
  `∑ k, (A' (θ ⬝ᵥ X k) - Y k) • X k`.
* `risk_eq_glmLoss`: logistic regression is the Bernoulli GLM (`A` = softplus, the Bernoulli
  log-partition function by `logPartition_bernoulli`); `glmLoss_sq`: for the quadratic `A z = z²/2`
  (the cumulant function of the unit-variance Gaussian family, not formalized here) the GLM loss is
  half the residual sum of squares minus a term depending only on the responses.

Measure-theoretic exponential families, as in Casella and Berger, *Statistical Inference*,
Chapter 3, are formalized in `FormalizedTextbooks/CasellaBergerStatisticalInference/Chapter3`
(`IsExponentialFamily`, and `convex_naturalParameterSpace` for the convexity of the natural
parameter space). This file treats finite sample spaces, where every natural parameter is
admissible, and develops the log-partition calculus used in machine learning.
-/

@[expose] public section

namespace Cslib.MachineLearning

namespace ExponentialFamily

open Finset Real Convexity

variable {X ι : Type*} [Fintype X] [Fintype ι]

/-! The definitions below accept any real `h`; they are the log-partition function, normalized
density, mean and likelihood of an exponential family when `h` is nonnegative with positive total
mass, which every theorem about them assumes (`hh`, `hpos`). -/

/-- The log-partition function `A η = log ∑ x, h x * exp (η ⬝ᵥ T x)` (for a base measure `h ≥ 0`
with positive total mass). -/
noncomputable def logPartition (h : X → ℝ) (T : X → ι → ℝ) (η : ι → ℝ) : ℝ :=
  log (∑ x, h x * exp (η ⬝ᵥ T x))

/-- The density `h x * exp (η ⬝ᵥ T x - A η)` (a probability mass function for a base measure
`h ≥ 0` with positive total mass, `sum_density`). -/
noncomputable def density (h : X → ℝ) (T : X → ι → ℝ) (η : ι → ℝ) (x : X) : ℝ :=
  h x * exp (η ⬝ᵥ T x - logPartition h T η)

/-- The mean of the sufficient statistic under `density h T η`. -/
noncomputable def mean (h : X → ℝ) (T : X → ι → ℝ) (η : ι → ℝ) : ι → ℝ :=
  ∑ x, density h T η x • T x

/-- The likelihood of observations `x k`. -/
noncomputable def likelihood (h : X → ℝ) (T : X → ι → ℝ) {m : ℕ} (x : Fin m → X) (η : ι → ℝ) :
    ℝ :=
  ∏ k, density h T η (x k)

variable {h : X → ℝ} (hh : ∀ x, 0 ≤ h x) (hpos : 0 < ∑ x, h x) (T : X → ι → ℝ)
include hh hpos

theorem partition_pos (η : ι → ℝ) : 0 < ∑ x, h x * exp (η ⬝ᵥ T x) := by
  refine lt_of_le_of_ne (sum_nonneg fun x _ => mul_nonneg (hh x) (exp_pos _).le) fun h0 => ?_
  have h0' := (sum_eq_zero_iff_of_nonneg fun x _ => mul_nonneg (hh x) (exp_pos _).le).1 h0.symm
  have hz : ∀ x, h x = 0 := fun x =>
    (mul_eq_zero.1 (h0' x (mem_univ x))).resolve_right (exp_pos _).ne'
  simp [hz] at hpos

theorem density_eq (η : ι → ℝ) (x : X) :
    density h T η x = h x * exp (η ⬝ᵥ T x) / ∑ y, h y * exp (η ⬝ᵥ T y) := by
  rw [density, exp_sub, logPartition, exp_log (partition_pos hh hpos T η), mul_div_assoc]

omit hpos in
theorem density_nonneg (η : ι → ℝ) (x : X) : 0 ≤ density h T η x :=
  mul_nonneg (hh x) (exp_pos _).le

/-- The density is a probability distribution. -/
theorem sum_density (η : ι → ℝ) : ∑ x, density h T η x = 1 := by
  simp only [density_eq hh hpos T, ← sum_div]
  exact div_self (partition_pos hh hpos T η).ne'

/-- The distribution with natural parameters `η`, a point of the standard simplex. -/
noncomputable def dist (η : ι → ℝ) : StdSimplex ℝ X :=
  StdSimplex.ofWeights (density h T η) (density_nonneg hh T η) (sum_density hh hpos T η)

@[simp]
theorem dist_weights (η : ι → ℝ) (x : X) : (dist hh hpos T η).weights x = density h T η x :=
  StdSimplex.ofWeights_weights _ _ _ x

/-- **The log-partition function is convex.** -/
theorem convexOn_logPartition : ConvexOn ℝ Set.univ (logPartition h T) := by
  refine ⟨convex_univ, fun η _ η' _ a b ha hb hab => ?_⟩
  have := (convexOn_log_sum_mul_exp hh hpos).2 (Set.mem_univ fun x => η ⬝ᵥ T x)
    (Set.mem_univ fun x => η' ⬝ᵥ T x) ha hb hab
  simpa [logPartition, add_dotProduct, smul_dotProduct] using this

/-- **The gradient of the log-partition function is the mean** of the sufficient statistic. -/
theorem hasFDerivAt_logPartition (η : ι → ℝ) :
    HasFDerivAt (logPartition h T) (dotL (mean h T η)) η := by
  have hsum : HasFDerivAt (fun η : ι → ℝ => ∑ x, h x * exp (η ⬝ᵥ T x))
      (∑ x, h x • (exp (η ⬝ᵥ T x) • dotL (T x))) η :=
    HasFDerivAt.fun_sum fun x _ => ((hasFDerivAt_dotProduct (T x) η).exp).const_mul (h x)
  have e : dotL (mean h T η) = (∑ x, h x * exp (η ⬝ᵥ T x))⁻¹ •
      ∑ x, h x • (exp (η ⬝ᵥ T x) • dotL (T x)) := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [mean, dotL_apply, dotProduct_sum, dotProduct_smul, smul_apply,
      _root_.sum_apply, smul_eq_mul, density_eq hh hpos T, Finset.mul_sum]
    exact sum_congr rfl fun x _ => by ring
  rw [e]
  exact hsum.log (partition_pos hh hpos T η).ne'

/-- The gradient of the log-partition function is the mean, in Mathlib's gradient API on
`EuclideanSpace ℝ ι`. -/
theorem hasGradientAt_logPartition (η : ι → ℝ) :
    HasGradientAt (fun u : EuclideanSpace ℝ ι => logPartition h T (WithLp.ofLp u))
      (WithLp.toLp 2 (mean h T η)) (WithLp.toLp 2 η) :=
  hasGradientAt_ofLp (hasFDerivAt_logPartition hh hpos T η)

/-- The derivative of the log-partition function at `η` in the direction `v` is
`v ⬝ᵥ mean η`. -/
theorem hasDerivAt_logPartition_line (η v : ι → ℝ) :
    HasDerivAt (fun t : ℝ => logPartition h T (η + t • v)) (v ⬝ᵥ mean h T η) 0 :=
  hasDerivAt_line_of_hasFDerivAt (hasFDerivAt_logPartition hh hpos T η) v

/-- The supporting-hyperplane inequality for the log-partition function. -/
theorem logPartition_sub_ge (η η' : ι → ℝ) :
    (η' - η) ⬝ᵥ mean h T η ≤ logPartition h T η' - logPartition h T η := by
  have hZ := partition_pos hh hpos T η
  -- Jensen: exp (∑ p x u x) ≤ ∑ p x exp (u x) with u x = (η' - η) ⬝ᵥ T x
  have hJ := convexOn_exp.map_sum_le (t := univ) (w := density h T η)
    (p := fun x => (η' - η) ⬝ᵥ T x) (fun x _ => density_nonneg hh T η x)
    (sum_density hh hpos T η) (fun x _ => Set.mem_univ _)
  have hrhs : ∑ x, density h T η x • exp ((η' - η) ⬝ᵥ T x) =
      exp (logPartition h T η' - logPartition h T η) := by
    rw [exp_sub, logPartition, logPartition, exp_log (partition_pos hh hpos T η'), exp_log hZ,
      sum_div]
    refine sum_congr rfl fun x _ => ?_
    rw [density_eq hh hpos T, smul_eq_mul, sub_dotProduct, exp_sub]
    field_simp
  have hlhs : ∑ x, density h T η x • ((η' - η) ⬝ᵥ T x) = (η' - η) ⬝ᵥ mean h T η := by
    rw [mean, dotProduct_sum]
    exact sum_congr rfl fun x _ => by rw [dotProduct_smul]
  rw [hrhs, hlhs] at hJ
  exact (exp_le_exp.1 hJ)

omit hh hpos in
theorem likelihood_eq {m : ℕ} (x : Fin m → X) (η : ι → ℝ) :
    likelihood h T x η = (∏ k, h (x k)) *
      exp ((η ⬝ᵥ ∑ k, T (x k)) - m * logPartition h T η) := by
  rw [likelihood]
  simp only [density]
  rw [prod_mul_distrib, ← exp_sum, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, dotProduct_sum]

/-- **Moment matching**: if `m • mean η★ = ∑ k, T (x k)` (for `m > 0`: the model mean of the
statistic equals its sample mean), then `η★` maximizes the likelihood. -/
theorem likelihood_le_of_mean_eq {m : ℕ} (x : Fin m → X) {η₀ : ι → ℝ}
    (hmean : (m : ℝ) • mean h T η₀ = ∑ k, T (x k)) (η : ι → ℝ) :
    likelihood h T x η ≤ likelihood h T x η₀ := by
  rw [likelihood_eq T, likelihood_eq T]
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (prod_nonneg fun k _ => hh (x k))
  have hineq := logPartition_sub_ge hh hpos T η₀ η
  rw [← hmean, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have : (η - η₀) ⬝ᵥ mean h T η₀ = η ⬝ᵥ mean h T η₀ - η₀ ⬝ᵥ mean h T η₀ := sub_dotProduct _ _ _
  nlinarith [mul_le_mul_of_nonneg_left hineq (Nat.cast_nonneg (α := ℝ) m)]

/-- The family as a normalized density family for counting measure: the interface of iid
likelihoods and maximum likelihood estimators in
`MathlibExt/Probability/Statistics/Likelihood.lean`. -/
noncomputable def densityFamily [MeasurableSpace X] [MeasurableSingletonClass X] :
    ProbabilityTheory.NormalizedDensityFamily X (ι → ℝ) MeasureTheory.Measure.count where
  dens η x := ENNReal.ofReal (density h T η x)
  measurable _ := (measurable_of_finite _).aemeasurable
  normalized η := by
    rw [MeasureTheory.lintegral_count, tsum_fintype,
      ← ENNReal.ofReal_sum_of_nonneg fun x _ => density_nonneg hh T η x, sum_density hh hpos T η,
      ENNReal.ofReal_one]

theorem iidLikelihood_eq [MeasurableSpace X] [MeasurableSingletonClass X] {m : ℕ}
    (x : Fin m → X) (η : ι → ℝ) :
    (densityFamily hh hpos T).iidLikelihood m η x = ENNReal.ofReal (likelihood h T x η) := by
  rw [ProbabilityTheory.NormalizedDensityFamily.iidLikelihood_apply, likelihood,
    ENNReal.ofReal_prod_of_nonneg fun k _ => density_nonneg hh T η (x k)]
  rfl

/-- Moment matching in the iid-likelihood interface. -/
theorem isMaxOn_iidLikelihood_of_mean_eq [MeasurableSpace X] [MeasurableSingletonClass X]
    {m : ℕ} (x : Fin m → X) {η₀ : ι → ℝ} (hmean : (m : ℝ) • mean h T η₀ = ∑ k, T (x k)) :
    IsMaxOn (fun η => (densityFamily hh hpos T).iidLikelihood m η x) Set.univ η₀ := fun η _ => by
  simp only [iidLikelihood_eq]
  exact ENNReal.ofReal_le_ofReal (likelihood_le_of_mean_eq hh hpos T x hmean η)

omit hh hpos in
/-- **The Bernoulli family**: on `Bool` with statistic `b ↦ [b]`, the log-partition function is
the softplus. -/
theorem logPartition_bernoulli (η : ℝ) :
    logPartition (fun _ : Bool => (1 : ℝ)) (fun (b : Bool) (_ : Unit) => LogisticRegression.ind b)
      (fun _ => η) = softplus η := by
  simp [logPartition, softplus, LogisticRegression.ind, dotProduct, add_comm]

omit hh hpos in
theorem density_bernoulli_true (η : ℝ) :
    density (fun _ : Bool => (1 : ℝ)) (fun (b : Bool) (_ : Unit) => LogisticRegression.ind b)
      (fun _ => η) true = sigmoid η := by
  rw [density, logPartition_bernoulli]
  simp only [LogisticRegression.ind, dotProduct, univ_unique, sum_singleton, ↓reduceIte, mul_one,
    one_mul, softplus]
  rw [exp_sub, exp_log (by positivity), sigmoid_def, exp_neg]
  field_simp
  ring

omit hh hpos in
/-- For the Bernoulli family the mean is the logistic function. -/
theorem mean_bernoulli (η : ℝ) :
    mean (fun _ : Bool => (1 : ℝ)) (fun (b : Bool) (_ : Unit) => LogisticRegression.ind b)
      (fun _ => η) () = sigmoid η := by
  rw [mean, Finset.sum_apply, Fintype.sum_bool, Pi.smul_apply, Pi.smul_apply,
    density_bernoulli_true]
  simp [LogisticRegression.ind]

omit hh hpos in
/-- **The Bernoulli family is the Bernoulli distribution** with success probability
`sigmoid η`, the model of logistic regression. -/
theorem dist_bernoulli (η : ℝ) :
    dist (fun _ => zero_le_one) (by simp) (fun (b : Bool) (_ : Unit) => LogisticRegression.ind b)
      (fun _ => η) = LogisticRegression.bernoulliDist (unitInterval.sigmoid η) := by
  have htrue := density_bernoulli_true η
  have hsum := sum_density (h := fun _ : Bool => (1 : ℝ)) (fun _ => zero_le_one) (by simp)
    (fun (b : Bool) (_ : Unit) => LogisticRegression.ind b) (fun _ => η)
  rw [Fintype.sum_bool, htrue] at hsum
  refine Convexity.StdSimplex.ext (Finsupp.ext fun b => ?_)
  rw [dist_weights, LogisticRegression.bernoulliDist_weights,
    unitInterval.coe_sigmoid]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    linarith
  · simp only [↓reduceIte, htrue]

end ExponentialFamily

/-! ## Generalized linear models -/

namespace GLM

open Finset Real

variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- The loss of a canonical generalized linear model with cumulant function `A`, features `X k` and
responses `Y k`. When `A` is the log-partition function of an exponential family and the responses
lie in its support, it is the negative log-likelihood up to terms not depending on `θ`. -/
noncomputable def glmLoss (A : ℝ → ℝ) (X : Fin m → ι → ℝ) (Y : Fin m → ℝ) (θ : ι → ℝ) : ℝ :=
  ∑ k, (A (θ ⬝ᵥ X k) - Y k * (θ ⬝ᵥ X k))

/-- **The GLM loss is convex** when the log-partition function is. -/
theorem convexOn_glmLoss {A : ℝ → ℝ} (hA : ConvexOn ℝ Set.univ A) (X : Fin m → ι → ℝ)
    (Y : Fin m → ℝ) : ConvexOn ℝ Set.univ (glmLoss A X Y) := by
  refine ⟨convex_univ, fun θ _ θ' _ a b ha hb hab => ?_⟩
  simp only [glmLoss, smul_eq_mul, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun k _ => ?_
  have h := hA.2 (Set.mem_univ (θ ⬝ᵥ X k)) (Set.mem_univ (θ' ⬝ᵥ X k)) ha hb hab
  simp only [smul_eq_mul] at h
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  nlinarith

/-- **The gradient of the GLM loss** is `∑ k, (A' (θ ⬝ᵥ X k) - Y k) • X k`. -/
theorem hasFDerivAt_glmLoss {A A' : ℝ → ℝ} (hA : ∀ z, HasDerivAt A (A' z) z)
    (X : Fin m → ι → ℝ) (Y : Fin m → ℝ) (θ : ι → ℝ) :
    HasFDerivAt (glmLoss A X Y) (dotL (∑ k, (A' (θ ⬝ᵥ X k) - Y k) • X k)) θ := by
  have hk : ∀ k, HasFDerivAt (fun θ : ι → ℝ => A (θ ⬝ᵥ X k) - Y k * (θ ⬝ᵥ X k))
      (A' (θ ⬝ᵥ X k) • dotL (X k) - Y k • dotL (X k)) θ := fun k =>
    ((hA (θ ⬝ᵥ X k)).comp_hasFDerivAt (f := fun θ : ι → ℝ => θ ⬝ᵥ X k) θ
      (hasFDerivAt_dotProduct (X k) θ)).sub ((hasFDerivAt_dotProduct (X k) θ).const_mul (Y k))
  have e : dotL (∑ k, (A' (θ ⬝ᵥ X k) - Y k) • X k) =
      ∑ k, (A' (θ ⬝ᵥ X k) • dotL (X k) - Y k • dotL (X k)) := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp [dotProduct_sum, dotProduct_smul, sub_mul]
  rw [e]
  exact HasFDerivAt.fun_sum fun k _ => hk k

/-- The gradient of the GLM loss, in Mathlib's gradient API on `EuclideanSpace ℝ ι`. -/
theorem hasGradientAt_glmLoss {A A' : ℝ → ℝ} (hA : ∀ z, HasDerivAt A (A' z) z)
    (X : Fin m → ι → ℝ) (Y : Fin m → ℝ) (θ : ι → ℝ) :
    HasGradientAt (fun u : EuclideanSpace ℝ ι => glmLoss A X Y (WithLp.ofLp u))
      (WithLp.toLp 2 (∑ k, (A' (θ ⬝ᵥ X k) - Y k) • X k)) (WithLp.toLp 2 θ) :=
  hasGradientAt_ofLp (hasFDerivAt_glmLoss hA X Y θ)

/-- The derivative of the GLM loss in a direction `v`. -/
theorem hasDerivAt_glmLoss_line {A A' : ℝ → ℝ} (hA : ∀ z, HasDerivAt A (A' z) z)
    (X : Fin m → ι → ℝ) (Y : Fin m → ℝ) (θ v : ι → ℝ) :
    HasDerivAt (fun t : ℝ => glmLoss A X Y (θ + t • v))
      (∑ k, (A' (θ ⬝ᵥ X k) - Y k) * (v ⬝ᵥ X k)) 0 := by
  convert hasDerivAt_line_of_hasFDerivAt (hasFDerivAt_glmLoss hA X Y θ) v using 1
  simp [dotProduct_sum, dotProduct_smul, mul_comm]

/-- **Logistic regression is the Bernoulli GLM**: its risk is the GLM loss with the softplus. -/
theorem risk_eq_glmLoss (X : Fin m → ι → ℝ) (Y : Fin m → Bool) (w : ι → ℝ) :
    LogisticRegression.risk X Y w =
      glmLoss softplus X (fun k => LogisticRegression.ind (Y k)) w := by
  rfl

/-- **Least squares as a GLM loss**: with the quadratic cumulant `A z = z² / 2` the GLM loss is
half the residual sum of squares, up to a term not depending on `θ`. -/
theorem glmLoss_sq (X : Fin m → ι → ℝ) (Y : Fin m → ℝ) (θ : ι → ℝ) :
    glmLoss (fun z => z ^ 2 / 2) X Y θ = ∑ k, ((Y k - θ ⬝ᵥ X k) ^ 2 - Y k ^ 2) / 2 := by
  refine sum_congr rfl fun k _ => ?_
  ring

end GLM

end Cslib.MachineLearning
