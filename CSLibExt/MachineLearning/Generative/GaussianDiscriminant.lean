/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Generative.NaiveBayes
public import MathlibExt.LinearAlgebra.Matrix.LogDetTrace
public import MathlibExt.LinearAlgebra.Matrix.WeightedScatter
public import MathlibExt.Probability.Distributions.GaussianDensity
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian discriminant analysis

Gaussian discriminant analysis models labelled data `(y, x)`, with classes `y` in a finite set `C`
and features `x : ι → ℝ`, by a class prior `π` and class-conditional Gaussian densities with
class means `μ c` and a covariance shared by all classes. The covariance enters through its
inverse, the precision matrix `S`: `gaussianDensity S μ` is MathlibExt's
`MetaMathlibExt.multivariateGaussianPDFReal` with covariance `S⁻¹`, which for positive definite `S`
equals `(2π)^(-n/2) √(det S) exp (-(x - μ)ᵀ S (x - μ) / 2)` and is the density of Mathlib's
`multivariateGaussian` measure (`multivariateGaussian_eq_withDensity_gaussianDensity`). In
dimension one it is Mathlib's `ProbabilityTheory.gaussianPDFReal` (`gaussianDensity_unit`).
Quadratic forms are Mathlib's `Matrix.toQuadraticForm'`, and the pooled scatter matrix is
MathlibExt's `MetaMathlibExt.weightedScatter` of the residuals (`scatter`). The definitions accept
any matrix `S`; they are the Gaussian density and joint density only when `S` is positive
definite, which every statistical result below assumes.

## Main results

* `posterior_eq_softmax`: with a shared covariance (a positive definite precision matrix) and a
  prior that is positive on every class, the posterior probability of class `c` is
  `exp (a c x) / ∑ c', exp (a c' x)` for the affine functions
  `a c x = log (π c) + (S μ c)ᵀ x - μ cᵀ S μ c / 2` (`discriminant`): linear discriminant
  analysis. With two classes, `posterior_true_eq_sigmoid`: the posterior is the logistic function
  of an affine function of `x`, as in logistic regression (Ng, CS229 lecture notes, Part IV).
* `joint_le_joint_iff`: for classes of positive prior, classifying by the largest joint
  probability (equivalently posterior) compares the affine discriminants.

The discriminants contain `log (π c)`, so these statements need positive prior probabilities: a
class of prior `0` has posterior exactly `0`, which no finite softmax or logistic score gives.
* `likelihood_le_mle`: for a fixed positive definite precision matrix, the likelihood of labelled
  data is maximized by the class frequencies and the class sample means (`mle`; a class without
  examples gets mean `0` by convention, and every mean is optimal for it). The prior part is the
  categorical estimate `Categorical.likelihood_le_mle`; the means part is the fact that, for a
  positive semidefinite `S`, the sample mean minimizes `∑ (x k - μ)ᵀ S (x k - μ)`.
* `likelihood_le_scatter_inv`: for a fixed prior and means, if the scatter matrix
  `(1/m) ∑ (x k - μ (y k)) (x k - μ (y k))ᵀ` is positive definite, it is the maximum likelihood
  covariance. (With too few or degenerate data the scatter matrix is singular, and then no
  positive definite covariance maximizes the likelihood in general.) The key inequality is
  `Matrix.PosDef.log_det_mul_le_trace` (`MathlibExt/LinearAlgebra/Matrix/LogDetTrace.lean`):
  `log (det A det B) ≤ tr (A B) - n` for positive definite `A`, `B`.
* `likelihood_le_mle_mleCov`: when the scatter matrix about the class sample means (`mleCov`) is
  positive definite, the class frequencies, class sample means and `mleCov` are the closed-form
  maximum likelihood estimates of Gaussian discriminant analysis; the estimated prior is a point
  of the simplex by construction, and the estimated precision is then positive definite
  (`posDef_mleCov_inv`).
-/

@[expose] public section

namespace Cslib.MachineLearning.GaussianDiscriminant

open Finset Matrix Real Categorical Convexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In this file `quad S v` abbreviates Mathlib's quadratic form `Matrix.toQuadraticForm' S v`,
that is `vᵀ S v`. -/
local notation "quad" => Matrix.toQuadraticForm'

private theorem quad_apply (S : Matrix ι ι ℝ) (v : ι → ℝ) : quad S v = v ⬝ᵥ (S *ᵥ v) := by
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']

/-- The expression `(2π)^(-n/2) √(det S)`, the Gaussian normalizer in precision form. -/
private noncomputable def normConst (S : Matrix ι ι ℝ) : ℝ :=
  (2 * π) ^ (-(Fintype.card ι : ℝ) / 2) * √S.det

private theorem normConst_pos {S : Matrix ι ι ℝ} (hS : 0 < S.det) : 0 < normConst S :=
  mul_pos (rpow_pos_of_pos (by positivity) _) (sqrt_pos.2 hS)

/-- The Gaussian density with mean `μ` and precision matrix `S`: MathlibExt's
`multivariateGaussianPDFReal` with covariance `S⁻¹`. For positive definite `S` it is the density
of the Gaussian with covariance `S⁻¹` (`multivariateGaussian_eq_withDensity_gaussianDensity`). -/
noncomputable def gaussianDensity (S : Matrix ι ι ℝ) (μ x : ι → ℝ) : ℝ :=
  MetaMathlibExt.multivariateGaussianPDFReal (WithLp.toLp 2 μ) S⁻¹ (WithLp.toLp 2 x)

/-- The precision form `(2π)^(-n/2) √(det S) exp (-(x - μ)ᵀ S (x - μ) / 2)` of the density, for
`det S > 0`. -/
private theorem gaussianDensity_eq {S : Matrix ι ι ℝ} (hS : 0 < S.det) (μ x : ι → ℝ) :
    gaussianDensity S μ x = normConst S * exp (-quad S (x - μ) / 2) := by
  symm
  rw [gaussianDensity, normConst, MetaMathlibExt.multivariateGaussianPDFReal,
    nonsing_inv_nonsing_inv S (isUnit_iff_ne_zero.2 hS.ne'), det_nonsing_inv,
    Ring.inverse_eq_inv', sqrt_inv, inv_inv, ← WithLp.toLp_sub, WithLp.ofLp_toLp]
  congr 1
  · rw [mul_comm ((√(2 * π) ^ Fintype.card ι)⁻¹), mul_comm ((2 * π) ^ _)]
    congr 1
    rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul (by positivity), ← rpow_neg (by positivity)]
    congr 1
    ring
  · rw [quad_apply]

theorem gaussianDensity_pos {S : Matrix ι ι ℝ} (hS : 0 < S.det) (μ x : ι → ℝ) :
    0 < gaussianDensity S μ x := by
  rw [gaussianDensity_eq hS]
  exact mul_pos (normConst_pos hS) (exp_pos _)

omit [Fintype ι] [DecidableEq ι] in
open scoped NNReal in
/-- In dimension one, with precision `1 / v`, this is Mathlib's Gaussian density with variance
`v`. -/
theorem gaussianDensity_unit (μ x : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianDensity (Matrix.of fun _ _ : Unit => (v : ℝ)⁻¹) (fun _ => μ) (fun _ => x) =
      ProbabilityTheory.gaussianPDFReal μ v x := by
  have hv' : (0 : ℝ) < v := by positivity
  rw [gaussianDensity_eq (by simpa [det_unique] using hv')]
  unfold normConst ProbabilityTheory.gaussianPDFReal
  simp only [Fintype.card_unit, Nat.cast_one, det_unique, of_apply, quad_apply]
  congr 1
  · rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring, rpow_neg (by positivity), ← sqrt_eq_rpow,
      sqrt_inv, ← mul_inv, ← sqrt_mul (by positivity)]
  · congr 1
    simp [dotProduct, mulVec]
    field_simp

/-- For positive definite `S`, `gaussianDensity S μ` is the density of Mathlib's multivariate
Gaussian measure with mean `μ` and covariance `S⁻¹` with respect to Lebesgue measure on
`EuclideanSpace ℝ ι`. -/
theorem multivariateGaussian_eq_withDensity_gaussianDensity {S : Matrix ι ι ℝ} (hS : S.PosDef)
    (μ : ι → ℝ) :
    ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 μ) S⁻¹ =
      MeasureTheory.volume.withDensity
        fun x => ENNReal.ofReal (gaussianDensity S μ (WithLp.ofLp x)) := by
  rw [MetaMathlibExt.multivariateGaussian_eq_withDensity _ hS.inv]
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- A positive definite real matrix is symmetric. -/
private theorem transpose_eq_of_posDef {S : Matrix ι ι ℝ} (hS : S.PosDef) : Sᵀ = S :=
  (show S.IsSymm by simpa [conjTranspose] using hS.1).eq

/-- Expanding `(x - μ)ᵀ S (x - μ)` for a symmetric `S`. -/
private theorem quad_sub {S : Matrix ι ι ℝ} (hS : Sᵀ = S) (x μ : ι → ℝ) :
    quad S (x - μ) = quad S x - 2 * ((S *ᵥ μ) ⬝ᵥ x) + quad S μ := by
  simp only [quad_apply, mulVec_sub, sub_dotProduct, dotProduct_sub]
  rw [IsSymm.dotProduct_mulVec_comm hS (x := μ) (y := x), dotProduct_comm (S *ᵥ μ) x]
  ring

/-! ## The posterior is a softmax of affine functions -/

/-- Parameters of Gaussian discriminant analysis with a shared covariance: a class prior, class
means, and the precision matrix (inverse covariance) shared by the classes. -/
structure Params (C ι : Type*) where
  /-- The class prior. -/
  prior : StdSimplex ℝ C
  /-- The class means. -/
  mean : C → ι → ℝ
  /-- The shared precision matrix (the inverse covariance when it is positive definite). -/
  prec : Matrix ι ι ℝ

namespace Params

variable {C : Type*} [Fintype C]

/-- The joint density of class `c` and features `x` (a density when the precision matrix is
positive definite). -/
noncomputable def joint (p : Params C ι) (c : C) (x : ι → ℝ) : ℝ :=
  p.prior.weights c * gaussianDensity p.prec (p.mean c) x

/-- The posterior score `joint c x / ∑ c', joint c' x`: the posterior probability of class `c`
when the denominator is positive, in particular for a positive definite precision matrix (Lean's
division makes every score `0` when the denominator is `0`). -/
noncomputable def posterior (p : Params C ι) (x : ι → ℝ) (c : C) : ℝ :=
  p.joint c x / ∑ c', p.joint c' x

/-- The linear discriminant `log (π c) + (S μ c)ᵀ x - μ cᵀ S μ c / 2`, affine in `x`. -/
noncomputable def discriminant (p : Params C ι) (c : C) (x : ι → ℝ) : ℝ :=
  log (p.prior.weights c) + (p.prec *ᵥ p.mean c) ⬝ᵥ x - quad p.prec (p.mean c) / 2

variable {p : Params C ι}

omit [Fintype C] in
/-- The joint density factors into the class-independent term `gaussianDensity p.prec 0 x` and the
exponential of the discriminant. -/
theorem joint_eq (hS : p.prec.PosDef) {c : C} (hc : 0 < p.prior.weights c) (x : ι → ℝ) :
    p.joint c x = gaussianDensity p.prec 0 x * exp (p.discriminant c x) := by
  rw [joint, gaussianDensity_eq hS.det_pos, gaussianDensity_eq hS.det_pos, sub_zero, discriminant,
    quad_sub (transpose_eq_of_posDef hS),
    show -(quad p.prec x - 2 * ((p.prec *ᵥ p.mean c) ⬝ᵥ x) + quad p.prec (p.mean c)) / 2 =
      -quad p.prec x / 2 + (log (p.prior.weights c) + (p.prec *ᵥ p.mean c) ⬝ᵥ x -
        quad p.prec (p.mean c) / 2) - log (p.prior.weights c) by ring,
    exp_sub, exp_add, exp_log hc]
  field_simp

/-- **Linear discriminant analysis**: with a shared covariance (a positive definite precision
matrix) and positive prior probabilities, the posterior is the softmax of the affine
discriminants. -/
theorem posterior_eq_softmax (hS : p.prec.PosDef) (hprior : ∀ c, 0 < p.prior.weights c)
    (x : ι → ℝ) (c : C) :
    p.posterior x c = exp (p.discriminant c x) / ∑ c', exp (p.discriminant c' x) := by
  have hK : 0 < gaussianDensity p.prec 0 x := gaussianDensity_pos hS.det_pos 0 x
  rw [posterior, joint_eq hS (hprior c), sum_congr rfl fun c' _ => joint_eq hS (hprior c') x,
    ← mul_sum, mul_div_mul_left _ _ hK.ne']

omit [Fintype C] in
/-- For classes of positive prior, comparing joint densities compares the affine
discriminants. -/
theorem joint_le_joint_iff (hS : p.prec.PosDef) {c c' : C} (hc : 0 < p.prior.weights c)
    (hc' : 0 < p.prior.weights c') (x : ι → ℝ) :
    p.joint c x ≤ p.joint c' x ↔ p.discriminant c x ≤ p.discriminant c' x := by
  rw [joint_eq hS hc, joint_eq hS hc', mul_le_mul_iff_right₀ (gaussianDensity_pos hS.det_pos 0 x),
    exp_le_exp]

/-- **Two classes**: with positive prior probabilities, the posterior of `true` is the logistic
function of the affine function with weights `S (μ true - μ false)`. -/
theorem posterior_true_eq_sigmoid {q : Params Bool ι} (hS : q.prec.PosDef)
    (hprior : ∀ c, 0 < q.prior.weights c) (x : ι → ℝ) :
    q.posterior x true = sigmoid ((q.prec *ᵥ (q.mean true - q.mean false)) ⬝ᵥ x +
      (log (q.prior.weights true / q.prior.weights false) -
        (quad q.prec (q.mean true) - quad q.prec (q.mean false)) / 2)) := by
  have h := Real.sigmoid_log_sub_log (exp_pos (q.discriminant true x))
    (exp_pos (q.discriminant false x))
  rw [posterior_eq_softmax hS hprior, Fintype.sum_bool, ← h, log_exp, log_exp]
  congr 1
  rw [discriminant, discriminant, log_div (hprior true).ne' (hprior false).ne', mulVec_sub,
    sub_dotProduct]
  ring

end Params

/-! ## Maximum likelihood estimation -/

section Mean

variable {κ : Type*}

/-- **Decomposition about the sample mean** `x̄ = s.centerMass 1 x`: for a symmetric `S`,
`∑ (x k - μ)ᵀ S (x k - μ) = ∑ (x k - x̄)ᵀ S (x k - x̄) + |s| (x̄ - μ)ᵀ S (x̄ - μ)`. -/
private theorem sum_quad_sub_centerMass {S : Matrix ι ι ℝ} (hS : Sᵀ = S) {s : Finset κ}
    (hs : s.Nonempty) (x : κ → ι → ℝ) (μ : ι → ℝ) :
    ∑ k ∈ s, quad S (x k - μ) =
      ∑ k ∈ s, quad S (x k - s.centerMass (fun _ => (1 : ℝ)) x) +
        s.card * quad S (s.centerMass (fun _ => (1 : ℝ)) x - μ) := by
  set m := s.centerMass (fun _ => (1 : ℝ)) x with hm
  have hsum : ∑ k ∈ s, (x k - m) = 0 := by
    rw [sum_sub_distrib, sum_const, hm, Finset.centerMass]
    simp only [one_smul, sum_const, Nat.smul_one_eq_cast]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hs.card_pos.ne'), one_smul, sub_self]
  have hk : ∀ k, quad S (x k - μ) = quad S (x k - m) + 2 * ((x k - m) ⬝ᵥ (S *ᵥ (m - μ))) +
      quad S (m - μ) := fun k => by
    have : x k - μ = (x k - m) + (m - μ) := by abel
    rw [this]
    simp only [quad_apply, mulVec_add, add_dotProduct, dotProduct_add]
    rw [IsSymm.dotProduct_mulVec_comm hS (x := m - μ) (y := x k - m)]
    ring
  rw [sum_congr rfl fun k _ => hk k, sum_add_distrib, sum_add_distrib, ← mul_sum, ← sum_dotProduct,
    hsum, zero_dotProduct, mul_zero, add_zero, sum_const, nsmul_eq_mul]

/-- For a positive semidefinite `S`, the sample mean minimizes `∑ (x k - μ)ᵀ S (x k - μ)`. -/
private theorem sum_quad_sub_centerMass_le {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (s : Finset κ)
    (x : κ → ι → ℝ) (μ : ι → ℝ) :
    ∑ k ∈ s, quad S (x k - s.centerMass (fun _ => (1 : ℝ)) x) ≤ ∑ k ∈ s, quad S (x k - μ) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hsymm : Sᵀ = S := (show S.IsSymm by simpa [conjTranspose] using hS.1).eq
  have : 0 ≤ quad S (s.centerMass (fun _ => (1 : ℝ)) x - μ) := by
    simpa [quad_apply] using hS.dotProduct_mulVec_nonneg (s.centerMass (fun _ => (1 : ℝ)) x - μ)
  rw [sum_quad_sub_centerMass hsymm hs x μ]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) this)

end Mean

namespace Params

variable {C : Type*} [Fintype C] [DecidableEq C] {m : ℕ} (y : Fin m → C) (x : Fin m → ι → ℝ)

/-- The likelihood of labelled data `(y k, x k)`. -/
noncomputable def likelihood (p : Params C ι) : ℝ :=
  ∏ k, p.joint (y k) (x k)

/-- The examples of class `c`. -/
def members (c : C) : Finset (Fin m) :=
  univ.filter fun k => y k = c

/-- The class sample means: Mathlib's `Finset.centerMass` of the examples of the class with unit
weights, `(1 / |members y c|) ∑ x k`; it is `0` for a class without examples, by Lean's convention
`0⁻¹ = 0`. -/
noncomputable def mleMean (c : C) : ι → ℝ :=
  (members y c).centerMass (fun _ => (1 : ℝ)) x

/-- Estimates of the prior and means for a given precision matrix `S`: the class frequencies and
the class sample means. When `S` is positive definite they maximize the likelihood
(`likelihood_le_mle`). -/
noncomputable def mle [Nonempty C] (S : Matrix ι ι ℝ) : Params C ι where
  prior := Categorical.mle (NaiveBayes.classCount y)
  mean := mleMean y x
  prec := S

private theorem likelihood_eq (p : Params C ι) (hS : 0 < p.prec.det) :
    likelihood y x p = Categorical.likelihood p.prior (NaiveBayes.classCount y) *
      (normConst p.prec ^ m *
        exp (-(∑ c, ∑ k ∈ members y c, quad p.prec (x k - p.mean c)) / 2)) := by
  rw [likelihood]
  simp only [joint, gaussianDensity_eq hS, Categorical.likelihood]
  rw [prod_mul_distrib, Fintype.prod_comp_eq_prod_pow y p.prior.weights, prod_mul_distrib,
    prod_const, card_univ, Fintype.card_fin, ← exp_sum, ← sum_div, ← sum_neg_distrib]
  congr 4
  rw [← sum_fiberwise univ y fun k => -quad p.prec (x k - p.mean (y k))]
  refine sum_congr rfl fun c _ => ?_
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun k hk => ?_
  rw [(mem_filter.1 hk).2]

/-- **Maximum likelihood estimation**: for a fixed positive definite precision matrix, the class
frequencies and class sample means maximize the likelihood over all priors and means. -/
theorem likelihood_le_mle [Nonempty C] {p : Params C ι} (hS : p.prec.PosDef) :
    likelihood y x p ≤ likelihood y x (mle y x p.prec) := by
  rw [likelihood_eq y x p hS.det_pos, likelihood_eq y x (mle y x p.prec) hS.det_pos]
  have hN : 0 ≤ normConst p.prec ^ m := pow_nonneg (normConst_pos hS.det_pos).le _
  refine mul_le_mul (Categorical.likelihood_le_mle _ _) ?_ (mul_nonneg hN (exp_pos _).le)
    (likelihood_nonneg _ _)
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) hN
  refine div_le_div_of_nonneg_right (neg_le_neg (sum_le_sum fun c _ => ?_)) (by norm_num)
  exact sum_quad_sub_centerMass_le hS.posSemidef _ x _

end Params

/-! ### The shared covariance -/

private theorem quad_eq_trace (S : Matrix ι ι ℝ) (d : ι → ℝ) :
    quad S d = (S * vecMulVec d d).trace := by
  rw [mul_vecMulVec, trace_vecMulVec, quad_apply, dotProduct_comm]

omit [Fintype ι] [DecidableEq ι] in
private theorem sqrt_pow_eq_exp {a : ℝ} (ha : 0 < a) (m : ℕ) : √a ^ m = exp (m * log a / 2) := by
  rw [← exp_log (sqrt_pos.2 ha), ← exp_nat_mul, log_sqrt ha.le]
  congr 1
  ring

/-- The inverse of a positive definite `T` maximizes `normConst S ^ m * exp (-m tr (S T) / 2)` over
positive definite `S`. -/
private theorem normConst_pow_mul_exp_le {S T : Matrix ι ι ℝ} (hS : S.PosDef) (hT : T.PosDef)
    (m : ℕ) :
    normConst S ^ m * exp (-(m * (S * T).trace) / 2) ≤
      normConst T⁻¹ ^ m * exp (-(m * (T⁻¹ * T).trace) / 2) := by
  have hTdet := hT.det_pos
  have hinv : T⁻¹.det = T.det⁻¹ := by
    rw [det_nonsing_inv, Ring.inverse_eq_inv']
  have htr : (T⁻¹ * T).trace = Fintype.card ι := by
    rw [nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hTdet.ne'), trace_one]
  simp only [normConst, mul_pow]
  rw [mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (rpow_pos_of_pos (by positivity) _).le _)
  rw [sqrt_pow_eq_exp hS.det_pos, sqrt_pow_eq_exp (by rw [hinv]; positivity), ← exp_add,
    ← exp_add, exp_le_exp, hinv, log_inv, htr]
  have key := hS.log_det_mul_le_trace hT
  rw [log_mul hS.det_pos.ne' hTdet.ne'] at key
  nlinarith [mul_le_mul_of_nonneg_left key (Nat.cast_nonneg (α := ℝ) m)]

namespace Params

variable {C : Type*} [Fintype C] [DecidableEq C] {m : ℕ} (y : Fin m → C) (x : Fin m → ι → ℝ)

/-- The pooled scatter matrix of the residuals `x k - μ (y k)` about the class means `μ`:
MathlibExt's `weightedScatter` of the residuals with unit weights about `0`, that is
`(m : ℝ)⁻¹ ∑ (x k - μ (y k)) (x k - μ (y k))ᵀ` (`scatter_eq`); the zero matrix for `m = 0`. -/
noncomputable def scatter (μ : C → ι → ℝ) : Matrix ι ι ℝ :=
  MetaMathlibExt.weightedScatter (fun _ => (1 : ℝ)) (fun k => WithLp.toLp 2 (x k - μ (y k))) 0

omit [Fintype ι] [DecidableEq ι] [Fintype C] [DecidableEq C] in
theorem scatter_eq (μ : C → ι → ℝ) :
    scatter y x μ = (m : ℝ)⁻¹ • ∑ k, vecMulVec (x k - μ (y k)) (x k - μ (y k)) := by
  simp [scatter, MetaMathlibExt.weightedScatter]

omit [Fintype ι] [DecidableEq ι] [Fintype C] [DecidableEq C] in
theorem scatter_transpose (μ : C → ι → ℝ) : (scatter y x μ)ᵀ = scatter y x μ :=
  MetaMathlibExt.weightedScatter_transpose _ _ _

omit [DecidableEq ι] [Fintype C] [DecidableEq C] in
open scoped RealInnerProductSpace in
/-- The pooled scatter matrix is positive definite when the residuals are not all in an affine
hyperplane (`MetaMathlibExt.weightedScatter_posDef`). -/
theorem posDef_scatter (μ : C → ι → ℝ)
    (hspan : ∀ v : EuclideanSpace ℝ ι, v ≠ 0 →
      ∃ i j, ⟪v, WithLp.toLp 2 (x i - μ (y i))⟫ ≠ ⟪v, WithLp.toLp 2 (x j - μ (y j))⟫) :
    (scatter y x μ).PosDef :=
  MetaMathlibExt.weightedScatter_posDef (fun _ => one_pos) hspan 0

/-- The covariance estimate: the scatter matrix about the class sample means. When it is positive
definite it is the maximum likelihood covariance (`likelihood_le_mle_mleCov`). -/
noncomputable def mleCov : Matrix ι ι ℝ :=
  scatter y x (mleMean y x)

private theorem sum_members_quad (S : Matrix ι ι ℝ) (μ : C → ι → ℝ) :
    ∑ c, ∑ k ∈ members y c, quad S (x k - μ c) = ∑ k, quad S (x k - μ (y k)) := by
  rw [← sum_fiberwise univ y fun k => quad S (x k - μ (y k))]
  refine sum_congr rfl fun c _ => sum_congr rfl fun k hk => ?_
  rw [(mem_filter.1 hk).2]

omit [Fintype C] [DecidableEq C] in
/-- The likelihood with the residuals summed over the examples. -/
private theorem likelihood_eq_prod (p : Params C ι) (hS : 0 < p.prec.det) :
    likelihood y x p = (∏ k, p.prior.weights (y k)) *
      (normConst p.prec ^ m * exp (-(∑ k, quad p.prec (x k - p.mean (y k))) / 2)) := by
  rw [likelihood]
  simp only [joint, gaussianDensity_eq hS]
  rw [prod_mul_distrib, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← exp_sum,
    ← sum_div, ← sum_neg_distrib]

omit [Fintype C] [DecidableEq C] in
private theorem sum_quad_eq_trace (hm : 0 < m) (S : Matrix ι ι ℝ) (μ : C → ι → ℝ) :
    ∑ k, quad S (x k - μ (y k)) = m * (S * scatter y x μ).trace := by
  rw [scatter_eq, Matrix.mul_smul, trace_smul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 hm.ne'), one_mul, Finset.mul_sum, trace_sum]
  exact sum_congr rfl fun k _ => quad_eq_trace S _

omit [Fintype C] [DecidableEq C] in
/-- **Maximum likelihood covariance**: for a fixed prior and fixed means, if the scatter matrix of
the residuals is positive definite, its inverse maximizes the likelihood over positive definite
precision matrices, that is, the scatter matrix is the maximum likelihood covariance. -/
theorem likelihood_le_scatter_inv {p : Params C ι} (hS : p.prec.PosDef)
    (hT : (scatter y x p.mean).PosDef) :
    likelihood y x p ≤ likelihood y x ⟨p.prior, p.mean, (scatter y x p.mean)⁻¹⟩ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [likelihood]
  rw [likelihood_eq_prod y x p hS.det_pos,
    likelihood_eq_prod y x ⟨p.prior, p.mean, (scatter y x p.mean)⁻¹⟩ hT.inv.det_pos]
  refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun k _ => p.prior.nonneg (y k))
  rw [sum_quad_eq_trace y x hm, sum_quad_eq_trace y x hm]
  exact normConst_pow_mul_exp_le hS hT m

/-- **Maximum likelihood estimation of Gaussian discriminant analysis**: if the scatter matrix
about the class sample means is positive definite, the class frequencies, the class sample means
and that scatter matrix (as covariance) maximize the likelihood over all priors, means and
positive definite precision matrices. -/
theorem likelihood_le_mle_mleCov [Nonempty C] {p : Params C ι} (hS : p.prec.PosDef)
    (hT : (mleCov y x).PosDef) :
    likelihood y x p ≤ likelihood y x (mle y x (mleCov y x)⁻¹) :=
  (likelihood_le_mle y x hS).trans (likelihood_le_scatter_inv y x (p := mle y x p.prec) hS hT)

omit [Fintype C] in
/-- The estimated precision matrix is positive definite when the scatter matrix is. -/
theorem posDef_mleCov_inv (hT : (mleCov y x).PosDef) : ((mleCov y x)⁻¹).PosDef :=
  hT.inv

end Params

end Cslib.MachineLearning.GaussianDiscriminant
