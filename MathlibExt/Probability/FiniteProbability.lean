/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import MathlibExt.Probability.Causality.CausalIdentification
public import MathlibExt.Probability.Statistics.LinearModel.Sampling

/-!
# Finite probability: moments, least squares and model-conditional intervals

Finite-sum expectation, variance and covariance for real weights on a finite type, least squares
for a line and in matrix form, and interval coverage stated only under an explicit sampling model.

## i. Overview

A finite distribution on a finite type `α` is a weight `p : α → ℝ` with `∀ x, 0 ≤ p x` and
`∑ x, p x = 1`. The two conditions are hypotheses, and each lemma assumes only those it uses.
Expectation is the finite sum `∑ x, p x * X x`, variance is `E[(X - E X) ^ 2]` and covariance is
`E[(X - E X) * (Y - E Y)]`. Linearity and bilinearity hold for every weight; the constant,
affine and centring rules use `∑ x, p x = 1`, and nonnegativity of the variance uses `0 ≤ p`.

Real weights are used instead of Mathlib's `PMF`, whose `ℝ≥0∞` values and Bochner-integral
moments need measurability and `toReal` bookkeeping, and instead of the `Finsupp`-valued
`Convexity.StdSimplex` (Mathlib's set `stdSimplex` of such weights is deprecated). Section E
relates the two: for `q : PMF α` the weights `(q a).toReal` sum to `1`, and the integral,
`ProbabilityTheory.variance` and `ProbabilityTheory.covariance` against `q.toMeasure` are the
finite sums of this file. As a sum, `expectation p X` is the dot product `p ⬝ᵥ X`, and the
sample mean equals Mathlib's uniform average `Finset.expect`.

Independence is the product form `p (x, y) = pX x * pY y` on a product type: product events
`s ×ˢ t` factor and the covariance of `f x` and `g y` vanishes. Zero covariance does not imply
independence (`exists_covariance_eq_zero_prob_ne`).

The sample statistics of data `x : ι → ℝ` are the moments of the empirical weight
`(card ι)⁻¹`. The sample mean and the divide-by-`(n - 1)` sample variance are ATLAS's
finite-population mean and variance `MathlibExt.Probability.Causality.popMean` and
`MathlibExt.Probability.Causality.popVar`, under the names used in this file; the divide-by-`n`
variance has no counterpart there. An i.i.d. sample `ω : ι → α` from `p` has weight
`∏ i, p (ω i)`; under it the divide-by-`(n - 1)` sample variance is unbiased (Bessel's
correction). Variances are finite because the type is finite.

For the line `a + b x`, the slope `S_xy / S_xx` and the intercept `ȳ - b̂ x̄` minimize the
residual sum of squares, and they are its unique minimizer exactly when `0 < S_xx`. In matrix
form, ATLAS's estimator `MathlibExt.Probability.Statistics.LinearModel.olsEstimator` solves the
normal equations `Xᵀ X β = Xᵀ y`, uniquely when `Xᵀ X` is invertible, equivalently when the
columns of `X` are linearly independent. For the design matrix with rows `(1, x i)` that estimator
is `(olsIntercept x y, olsSlope x y)`. These algebraic facts say nothing about the distribution of
the noise.

An interval obtained by inverting a pivot is a set computed from data. Its coverage probability
is the probability of the acceptance region under the law of the pivot. That law is a hypothesis
of `measure_mem_pivotInterval` and of the normal-location statement `measure_mem_zInterval`, not
part of any definition. A posterior credible interval is defined by its posterior probability, so
its coverage under the posterior is definitional.

## ii. Key results

- `expectation_linear`, `expectation_indicator`, `sum_prob_filter_eq` : linearity, indicators and
  total probability.
- `variance_nonneg`, `variance_affine`, `covariance_sum_mul_sum`, `covMatrix_mulVec` : second
  moments and linear maps.
- `covariance_prod_eq_zero`, `exists_covariance_eq_zero_prob_ne` : independence gives zero
  covariance, and the converse fails.
- `expectation_sampleVarUnbiased` : Bessel's correction for i.i.d. finite samples.
- `normalEquations_iff`, `ols_unique_minimizer_iff`, `eq_olsEstimator_iff`,
  `olsEstimator_designMatrix` : least squares.
- `measure_mem_pivotInterval`, `measure_mem_zInterval`,
  `IsCredibleInterval.expectation_indicator_eq` : intervals under a stated model.

## iii. Table of contents

- A. Expectation and events
- B. Variance and covariance
- C. Covariance matrices
- D. Product weights and independence
- E. Comparison with `PMF` moments
- F. Sample statistics and i.i.d. samples
- G. Least squares for a line
- H. Least squares in matrix form
- I. Intervals under a sampling model

## iv. References

- ATLAS MF06 planning anchors R06 (Physlib canonical ensembles and finite partition functions)
  and R11 (Mathlib and MathlibExt substrate).
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Probability.FiniteProbability

/-! ## A. Expectation and events -/

/-- The expectation `∑ x, p x * X x` of `X : α → ℝ` under a weight `p : α → ℝ` on a finite type
(MF06.1). For a finite distribution (`0 ≤ p`, `∑ x, p x = 1`) this is the mean of `X`. Mathlib's
`μ[X]` and ATLAS `PMF.expect` are Bochner integrals against a measure; this finite sum needs no
measurability or `ℝ≥0∞` conversion (`integral_toMeasure_eq_expectation` relates them). As a
function of `p` and `X` it is the dot product `p ⬝ᵥ X` (`expectation_eq_dotProduct`); the
separate name carries the probabilistic API. -/
noncomputable def expectation {α : Type*} [Fintype α] (p X : α → ℝ) : ℝ :=
  ∑ x, p x * X x

lemma expectation_eq_dotProduct {α : Type*} [Fintype α] (p X : α → ℝ) :
    expectation p X = p ⬝ᵥ X :=
  rfl

/-- The probability `∑ x ∈ s, p x` of the event `s` under the weight `p` (MF06.1). Mathlib's
event probabilities are values of a measure in `ℝ≥0∞`; this is the real finite sum. -/
noncomputable def prob {α : Type*} (p : α → ℝ) (s : Finset α) : ℝ :=
  ∑ x ∈ s, p x

/-- The expectation of a constant is that constant. -/
lemma expectation_const {α : Type*} [Fintype α] {p : α → ℝ} (hp : ∑ x, p x = 1) (c : ℝ) :
    expectation p (fun _ => c) = c := by
  rw [expectation, ← Finset.sum_mul, hp, one_mul]

lemma expectation_add {α : Type*} [Fintype α] (p X Y : α → ℝ) :
    expectation p (fun x => X x + Y x) = expectation p X + expectation p Y := by
  simp only [expectation, mul_add, Finset.sum_add_distrib]

lemma expectation_sub {α : Type*} [Fintype α] (p X Y : α → ℝ) :
    expectation p (fun x => X x - Y x) = expectation p X - expectation p Y := by
  simp only [expectation, mul_sub, Finset.sum_sub_distrib]

lemma expectation_const_mul {α : Type*} [Fintype α] (p X : α → ℝ) (c : ℝ) :
    expectation p (fun x => c * X x) = c * expectation p X := by
  rw [expectation, expectation, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Expectation is linear, `E[a X + b Y] = a E[X] + b E[Y]`, for every weight. -/
lemma expectation_linear {α : Type*} [Fintype α] (p X Y : α → ℝ) (a b : ℝ) :
    expectation p (fun x => a * X x + b * Y x) = a * expectation p X + b * expectation p Y := by
  rw [expectation_add p (fun x => a * X x) (fun x => b * Y x), expectation_const_mul,
    expectation_const_mul]

lemma expectation_sum {α ι : Type*} [Fintype α] (p : α → ℝ) (s : Finset ι)
    (X : ι → α → ℝ) :
    expectation p (fun x => ∑ i ∈ s, X i x) = ∑ i ∈ s, expectation p (X i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

/-- The expectation of the indicator of an event is the probability of the event. -/
lemma expectation_indicator {α : Type*} [Fintype α] (p : α → ℝ) (E : α → Prop)
    [DecidablePred E] :
    expectation p (fun x => if E x then 1 else 0) = prob p (univ.filter E) := by
  simp only [expectation, prob, Finset.sum_filter, mul_ite, mul_one, mul_zero]

lemma prob_univ {α : Type*} [Fintype α] {p : α → ℝ} (hp : ∑ x, p x = 1) : prob p univ = 1 :=
  hp

lemma prob_nonneg {α : Type*} {p : α → ℝ} (hp0 : ∀ x, 0 ≤ p x) (s : Finset α) :
    0 ≤ prob p s :=
  Finset.sum_nonneg fun x _ => hp0 x

/-- Total probability for the two-set partition `{t, tᶜ}`: `P(s) = P(s ∩ t) + P(s \ t)`. -/
lemma prob_inter_add_prob_sdiff {α : Type*} [DecidableEq α] (p : α → ℝ) (s t : Finset α) :
    prob p (s ∩ t) + prob p (s \ t) = prob p s :=
  Finset.sum_inter_add_sum_sdiff s t p

lemma prob_add_prob_compl {α : Type*} [Fintype α] [DecidableEq α] {p : α → ℝ}
    (hp : ∑ x, p x = 1) (s : Finset α) : prob p s + prob p sᶜ = 1 := by
  rw [prob, prob, Finset.sum_add_sum_compl, hp]

/-- **Law of total probability** for the finite partition of `α` into the fibres of `f`. -/
theorem sum_prob_filter_eq {α ι : Type*} [Fintype ι] [DecidableEq ι] (p : α → ℝ) (f : α → ι)
    (s : Finset α) : ∑ i, prob p (s.filter fun x => f x = i) = prob p s :=
  Finset.sum_fiberwise s f p

/-- Dividing a weight by its partition function `∑ y, w y` gives total mass `1`. -/
lemma sum_div_sum_eq_one {α : Type*} [Fintype α] {w : α → ℝ} (hw : ∑ x, w x ≠ 0) :
    ∑ x, w x / ∑ y, w y = 1 := by
  rw [← Finset.sum_div, div_self hw]

/-- Under the normalized weight `w / Z`, `Z = ∑ y, w y`, the expectation is `Z⁻¹ ∑ x, w x X x`. -/
lemma expectation_div_sum {α : Type*} [Fintype α] (w X : α → ℝ) :
    expectation (fun x => w x / ∑ y, w y) X = (∑ x, w x * X x) / ∑ x, w x := by
  rw [expectation, Finset.sum_div]
  exact Finset.sum_congr rfl fun x _ => div_mul_eq_mul_div _ _ _

/-! ## B. Variance and covariance -/

/-- The covariance `E[(X - E X) * (Y - E Y)]` under the weight `p` (MF06.2). Mathlib's
`ProbabilityTheory.covariance` integrates against a measure and its algebra needs `MemLp`
hypotheses; this finite sum needs none (`covariance_toMeasure_eq` relates them). -/
noncomputable def covariance {α : Type*} [Fintype α] (p X Y : α → ℝ) : ℝ :=
  expectation p fun x => (X x - expectation p X) * (Y x - expectation p Y)

/-- The variance `E[(X - E X) ^ 2]` under the weight `p` (MF06.2). Mathlib's
`ProbabilityTheory.variance` is defined through `evariance` against a measure;
`variance_toMeasure_eq` relates the two. -/
noncomputable def variance {α : Type*} [Fintype α] (p X : α → ℝ) : ℝ :=
  expectation p fun x => (X x - expectation p X) ^ 2

lemma covariance_self {α : Type*} [Fintype α] (p X : α → ℝ) :
    covariance p X X = variance p X := by
  simp only [covariance, variance, sq]

lemma covariance_comm {α : Type*} [Fintype α] (p X Y : α → ℝ) :
    covariance p X Y = covariance p Y X := by
  simp only [covariance]
  congr 1
  funext x
  ring

lemma variance_nonneg {α : Type*} [Fintype α] {p : α → ℝ} (hp0 : ∀ x, 0 ≤ p x) (X : α → ℝ) :
    0 ≤ variance p X :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hp0 x) (sq_nonneg _)

lemma covariance_eq_sub {α : Type*} [Fintype α] {p : α → ℝ} (hp : ∑ x, p x = 1)
    (X Y : α → ℝ) :
    covariance p X Y =
      expectation p (fun x => X x * Y x) - expectation p X * expectation p Y := by
  have h : (fun x => (X x - expectation p X) * (Y x - expectation p Y)) = fun x =>
      X x * Y x - expectation p Y * X x -
        (expectation p X * Y x - expectation p X * expectation p Y) := by
    funext x
    ring
  rw [covariance, h, expectation_sub, expectation_sub, expectation_sub, expectation_const_mul,
    expectation_const_mul, expectation_const hp]
  ring

lemma variance_eq_sub {α : Type*} [Fintype α] {p : α → ℝ} (hp : ∑ x, p x = 1) (X : α → ℝ) :
    variance p X = expectation p (fun x => X x ^ 2) - expectation p X ^ 2 := by
  rw [← covariance_self, covariance_eq_sub hp]
  simp only [sq]

/-- `Var (a X + b) = a ^ 2 Var X`. -/
lemma variance_affine {α : Type*} [Fintype α] {p : α → ℝ} (hp : ∑ x, p x = 1) (X : α → ℝ)
    (a b : ℝ) : variance p (fun x => a * X x + b) = a ^ 2 * variance p X := by
  have hE : expectation p (fun x => a * X x + b) = a * expectation p X + b := by
    rw [expectation_add p (fun x => a * X x) (fun _ => b), expectation_const_mul,
      expectation_const hp]
  rw [variance, variance, hE,
    ← expectation_const_mul p (fun x => (X x - expectation p X) ^ 2) (a ^ 2)]
  congr 1
  funext x
  ring

/-- Covariance is linear in its first argument, for every weight. -/
lemma covariance_linear_left {α : Type*} [Fintype α] (p X₁ X₂ Y : α → ℝ) (a b : ℝ) :
    covariance p (fun x => a * X₁ x + b * X₂ x) Y =
      a * covariance p X₁ Y + b * covariance p X₂ Y := by
  calc covariance p (fun x => a * X₁ x + b * X₂ x) Y
      = expectation p (fun x => a * ((X₁ x - expectation p X₁) * (Y x - expectation p Y)) +
          b * ((X₂ x - expectation p X₂) * (Y x - expectation p Y))) := by
        rw [covariance, expectation_linear p X₁ X₂ a b]
        congr 1
        funext x
        ring
    _ = a * covariance p X₁ Y + b * covariance p X₂ Y := expectation_linear p _ _ a b

/-- Covariance is linear in its second argument, for every weight. -/
lemma covariance_linear_right {α : Type*} [Fintype α] (p X Y₁ Y₂ : α → ℝ) (a b : ℝ) :
    covariance p X (fun x => a * Y₁ x + b * Y₂ x) =
      a * covariance p X Y₁ + b * covariance p X Y₂ := by
  rw [covariance_comm, covariance_linear_left, covariance_comm p Y₁, covariance_comm p Y₂]

/-- Bilinearity of covariance in the finite-sum form
`cov (∑ i, a i X i, ∑ j, b j Y j) = ∑ i, ∑ j, a i b j cov (X i, Y j)`, for every weight. -/
lemma covariance_sum_mul_sum {α ι κ : Type*} [Fintype α] (p : α → ℝ) (s : Finset ι)
    (t : Finset κ) (a : ι → ℝ) (b : κ → ℝ) (X : ι → α → ℝ) (Y : κ → α → ℝ) :
    covariance p (fun x => ∑ i ∈ s, a i * X i x) (fun x => ∑ j ∈ t, b j * Y j x) =
      ∑ i ∈ s, ∑ j ∈ t, a i * b j * covariance p (X i) (Y j) := by
  have hX : expectation p (fun x => ∑ i ∈ s, a i * X i x) =
      ∑ i ∈ s, a i * expectation p (X i) := by
    rw [expectation_sum]
    exact Finset.sum_congr rfl fun i _ => expectation_const_mul p (X i) (a i)
  have hY : expectation p (fun x => ∑ j ∈ t, b j * Y j x) =
      ∑ j ∈ t, b j * expectation p (Y j) := by
    rw [expectation_sum]
    exact Finset.sum_congr rfl fun j _ => expectation_const_mul p (Y j) (b j)
  have key : ∀ x, (∑ i ∈ s, a i * X i x - ∑ i ∈ s, a i * expectation p (X i)) *
      (∑ j ∈ t, b j * Y j x - ∑ j ∈ t, b j * expectation p (Y j)) =
      ∑ i ∈ s, ∑ j ∈ t, a i * b j *
        ((X i x - expectation p (X i)) * (Y j x - expectation p (Y j))) := by
    intro x
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [covariance, hX, hY]
  simp_rw [key]
  rw [expectation_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [expectation_sum]
  exact Finset.sum_congr rfl fun j _ => expectation_const_mul p _ _

/-- The two-state (Bernoulli) weight `(1 - q, q)` on `Fin 2`: the indicator `(0, 1)` has mean
`q`. For `0 ≤ q ≤ 1` this weight is a finite distribution; the identity is algebraic. -/
lemma expectation_two_state (q : ℝ) : expectation ![1 - q, q] ![0, 1] = q := by
  simp [expectation, Fin.sum_univ_two]

/-- The two-state (Bernoulli) weight `(1 - q, q)` on `Fin 2`: the indicator `(0, 1)` has
variance `q (1 - q)`. -/
lemma variance_two_state (q : ℝ) : variance ![1 - q, q] ![0, 1] = q * (1 - q) := by
  rw [variance, expectation_two_state]
  simp [expectation, Fin.sum_univ_two]
  ring

/-! ## C. Covariance matrices -/

/-- The covariance matrix of the finite random vector `X : α → n → ℝ` (outcome `x` ↦ vector
`X x`): entry `(i, j)` is the covariance of coordinates `i` and `j` (MF06.2). Mathlib's
`ProbabilityTheory.covarianceBilin` is a bilinear form for measures on a normed space; this is
the matrix of pairwise finite covariances. -/
noncomputable def covMatrix {α n : Type*} [Fintype α] (p : α → ℝ) (X : α → n → ℝ) :
    Matrix n n ℝ :=
  Matrix.of fun i j => covariance p (fun x => X x i) (fun x => X x j)

lemma covMatrix_apply {α n : Type*} [Fintype α] (p : α → ℝ) (X : α → n → ℝ) (i j : n) :
    covMatrix p X i j = covariance p (fun x => X x i) (fun x => X x j) :=
  rfl

lemma covMatrix_apply_self {α n : Type*} [Fintype α] (p : α → ℝ) (X : α → n → ℝ) (i : n) :
    covMatrix p X i i = variance p (fun x => X x i) :=
  covariance_self _ _

lemma transpose_covMatrix {α n : Type*} [Fintype α] (p : α → ℝ) (X : α → n → ℝ) :
    (covMatrix p X)ᵀ = covMatrix p X := by
  ext i j
  exact covariance_comm _ _ _

/-- **Covariance under a linear map**: `cov (A X) = A cov (X) Aᵀ`, for every weight. -/
lemma covMatrix_mulVec {α m n : Type*} [Fintype α] [Fintype n] (p : α → ℝ) (A : Matrix m n ℝ)
    (X : α → n → ℝ) : covMatrix p (fun x => A *ᵥ X x) = A * covMatrix p X * Aᵀ := by
  ext i j
  have h := covariance_sum_mul_sum p univ univ (A i) (A j) (fun k x => X x k)
    (fun l x => X x l)
  simp only [covMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct]
  rw [h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

/-! ## D. Product weights and independence -/

lemma sum_prod_weight_eq_one {α β : Type*} [Fintype α] [Fintype β] {pX : α → ℝ} {pY : β → ℝ}
    (hX : ∑ x, pX x = 1) (hY : ∑ y, pY y = 1) : ∑ z : α × β, pX z.1 * pY z.2 = 1 := by
  rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, hX, hY, one_mul]

/-- Under the product weight `pX x * pY y`, the expectation of `f x * g y` factors. -/
lemma expectation_prod_mul {α β : Type*} [Fintype α] [Fintype β] (pX : α → ℝ) (pY : β → ℝ)
    (f : α → ℝ) (g : β → ℝ) :
    expectation (fun z : α × β => pX z.1 * pY z.2) (fun z => f z.1 * g z.2) =
      expectation pX f * expectation pY g := by
  rw [expectation, expectation, expectation, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

lemma expectation_prod_fst {α β : Type*} [Fintype α] [Fintype β] (pX : α → ℝ) {pY : β → ℝ}
    (hY : ∑ y, pY y = 1) (f : α → ℝ) :
    expectation (fun z : α × β => pX z.1 * pY z.2) (fun z => f z.1) = expectation pX f := by
  have h := expectation_prod_mul pX pY f fun _ => 1
  simp only [mul_one] at h
  rw [h, expectation_const hY, mul_one]

lemma expectation_prod_snd {α β : Type*} [Fintype α] [Fintype β] {pX : α → ℝ} (pY : β → ℝ)
    (hX : ∑ x, pX x = 1) (g : β → ℝ) :
    expectation (fun z : α × β => pX z.1 * pY z.2) (fun z => g z.2) = expectation pY g := by
  have h := expectation_prod_mul pX pY (fun _ => 1) g
  simp only [one_mul] at h
  rw [h, expectation_const hX, one_mul]

/-- Under the product weight, product events factor: `P(s ×ˢ t) = P_X(s) P_Y(t)`. -/
lemma prob_prod {α β : Type*} (pX : α → ℝ) (pY : β → ℝ) (s : Finset α) (t : Finset β) :
    prob (fun z : α × β => pX z.1 * pY z.2) (s ×ˢ t) = prob pX s * prob pY t := by
  rw [prob, prob, prob, Finset.sum_product, Finset.sum_mul_sum]

/-- **Independence implies zero covariance**: under the product weight `pX x * pY y` of two
finite distributions, `f x` and `g y` have covariance `0`. -/
lemma covariance_prod_eq_zero {α β : Type*} [Fintype α] [Fintype β] {pX : α → ℝ}
    {pY : β → ℝ} (hX : ∑ x, pX x = 1) (hY : ∑ y, pY y = 1) (f : α → ℝ) (g : β → ℝ) :
    covariance (fun z : α × β => pX z.1 * pY z.2) (fun z => f z.1) (fun z => g z.2) = 0 := by
  rw [covariance_eq_sub (sum_prod_weight_eq_one hX hY), expectation_prod_mul,
    expectation_prod_fst pX hY, expectation_prod_snd pY hX, sub_self]

/-- **Zero covariance does not imply independence.** Under the uniform weight on `Fin 3`,
`X = (-1, 0, 1)` and `Y = X ^ 2` have covariance `0`, but the events `{X = 0}` and `{Y = 0}` have
joint probability `1 / 3`, while the product of their probabilities is `1 / 9`. -/
lemma exists_covariance_eq_zero_prob_ne :
    ∃ p X : Fin 3 → ℝ, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
      covariance p X (fun i => X i ^ 2) = 0 ∧
      prob p (univ.filter fun i => X i = 0 ∧ X i ^ 2 = 0) ≠
        prob p (univ.filter fun i => X i = 0) * prob p (univ.filter fun i => X i ^ 2 = 0) := by
  refine ⟨fun _ => 1 / 3, ![-1, 0, 1], fun _ => by norm_num, ?_, ?_, ?_⟩
  · simp only [Fin.sum_univ_three]
    norm_num
  · simp only [covariance, expectation, Fin.sum_univ_three]
    norm_num
  · simp only [prob, Finset.sum_filter, Fin.sum_univ_three]
    norm_num

/-! ## E. Comparison with `PMF` moments -/

/-- The real weights `(q a).toReal` of a probability mass function on a finite type sum to `1`. -/
lemma sum_toReal_eq_one {α : Type*} [Fintype α] (q : PMF α) : ∑ a, (q a).toReal = 1 := by
  have h : ∑ a, q a = 1 := (tsum_fintype fun a => q a).symm.trans q.tsum_coe
  rw [← ENNReal.toReal_sum fun a _ => q.apply_ne_top a, h, ENNReal.toReal_one]

open MeasureTheory in
/-- Mathlib's integral against `q.toMeasure` is `expectation` for the weights `(q a).toReal`. -/
lemma integral_toMeasure_eq_expectation {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (q : PMF α) (X : α → ℝ) :
    ∫ a, X a ∂q.toMeasure = expectation (fun a => (q a).toReal) X := by
  rw [PMF.integral_eq_sum]
  rfl

/-- Mathlib's `ProbabilityTheory.covariance` against `q.toMeasure` is `covariance` for the
weights `(q a).toReal`. -/
lemma covariance_toMeasure_eq {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (q : PMF α) (X Y : α → ℝ) :
    ProbabilityTheory.covariance X Y q.toMeasure = covariance (fun a => (q a).toReal) X Y := by
  simp only [ProbabilityTheory.covariance, integral_toMeasure_eq_expectation]
  rfl

/-- Mathlib's `ProbabilityTheory.variance` against `q.toMeasure` is `variance` for the weights
`(q a).toReal`. -/
lemma variance_toMeasure_eq {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (q : PMF α) (X : α → ℝ) :
    ProbabilityTheory.variance X q.toMeasure = variance (fun a => (q a).toReal) X := by
  rw [ProbabilityTheory.variance_eq_integral Measurable.of_discrete.aemeasurable]
  simp only [integral_toMeasure_eq_expectation]
  rfl

/-! ## F. Sample statistics and i.i.d. samples -/

/-- The sample mean `x̄ = (∑ i, x i) / n` of data `x : ι → ℝ`, `n = card ι` (MF06.3). It is
ATLAS's finite-population mean `MathlibExt.Probability.Causality.popMean`, under the name used
by the sample statistics below (`sampleMean_eq_sum_div`), and it equals Mathlib's uniform
average `Finset.expect` over `univ` (`Fintype.expect_eq_sum_div_card`). -/
noncomputable def sampleMean {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  MathlibExt.Probability.Causality.popMean x

/-- The divide-by-`n` sample variance `(∑ i, (x i - x̄) ^ 2) / n` (MF06.3). Mathlib has no
sample variance of real data; Batteries' `RunningStats.sampleVariance` is a `Float` accumulator.
ATLAS's `MathlibExt.Probability.Causality` has no counterpart: its `popVar` and its
`Finset`-indexed `sampleVar` divide by `n - 1` and `|S| - 1`. -/
noncomputable def sampleVar {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  (∑ i, (x i - sampleMean x) ^ 2) / Fintype.card ι

/-- The divide-by-`(n - 1)` sample variance `(∑ i, (x i - x̄) ^ 2) / (n - 1)`, meant for
`2 ≤ n` (MF06.3); it is unbiased for i.i.d. samples (`expectation_sampleVarUnbiased`). It is
ATLAS's finite-population variance `MathlibExt.Probability.Causality.popVar`, under the name
used here (`sampleVarUnbiased_eq_sum_div`). For `n ≤ 1` the value is a junk `0`: the sum is
empty for `n = 0`, and `n = 1` divides by `0`. -/
noncomputable def sampleVarUnbiased {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  MathlibExt.Probability.Causality.popVar x

lemma sampleMean_eq_sum_div {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    sampleMean x = (∑ i, x i) / Fintype.card ι :=
  rfl

lemma sampleVarUnbiased_eq_sum_div {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    sampleVarUnbiased x = (∑ i, (x i - sampleMean x) ^ 2) / ((Fintype.card ι : ℝ) - 1) :=
  rfl

lemma card_mul_sampleMean {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    (Fintype.card ι : ℝ) * sampleMean x = ∑ i, x i := by
  rw [sampleMean_eq_sum_div, ← Fintype.expect_eq_sum_div_card, Fintype.card_mul_expect]

/-- The deviations from the sample mean sum to zero. -/
lemma sum_sub_sampleMean {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ∑ i, (x i - sampleMean x) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_mul_sampleMean, sub_self]

lemma sum_sq_sub_sampleMean {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ∑ i, (x i - sampleMean x) ^ 2 = ∑ i, x i ^ 2 - Fintype.card ι * sampleMean x ^ 2 := by
  have h : ∀ i, (x i - sampleMean x) ^ 2 =
      x i ^ 2 - 2 * sampleMean x * x i + sampleMean x ^ 2 := fun i => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← card_mul_sampleMean x]
  ring

/-- The sample mean is the expectation under the empirical weight `(card ι)⁻¹`. -/
lemma sampleMean_eq_expectation {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    sampleMean x = expectation (fun _ => (Fintype.card ι : ℝ)⁻¹) x := by
  rw [sampleMean_eq_sum_div, expectation, ← Finset.mul_sum, div_eq_inv_mul]

/-- The divide-by-`n` sample variance is the variance under the empirical weight. -/
lemma sampleVar_eq_variance {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    sampleVar x = variance (fun _ => (Fintype.card ι : ℝ)⁻¹) x := by
  rw [sampleVar, variance, ← sampleMean_eq_expectation x, expectation, ← Finset.mul_sum,
    div_eq_inv_mul]

/-- The empirical weight of a nonempty finite index type is a finite distribution. -/
lemma sum_inv_card_eq_one {ι : Type*} [Fintype ι] [Nonempty ι] :
    ∑ _ : ι, (Fintype.card ι : ℝ)⁻¹ = 1 := by
  simp [Finset.card_univ]

/-- Under the i.i.d. weight `∏ i, p (ω i)` on samples `ω : ι → α`, the expectation of a product
of functions of distinct coordinates is the product of the expectations. -/
lemma expectation_pi_prod {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι] (p : α → ℝ)
    (g : ι → α → ℝ) :
    expectation (fun ω : ι → α => ∏ i, p (ω i)) (fun ω => ∏ i, g i (ω i)) =
      ∏ i, expectation p (g i) := by
  simp only [expectation, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun i a => p a * g i a).symm

/-- The i.i.d. weight of a finite distribution is a finite distribution. -/
lemma sum_pi_prod_eq_one {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι] {p : α → ℝ}
    (hp : ∑ a, p a = 1) : ∑ ω : ι → α, ∏ i, p (ω i) = 1 := by
  have h := expectation_pi_prod p fun (_ : ι) (_ : α) => (1 : ℝ)
  simp only [expectation, mul_one, Finset.prod_const_one, hp] at h
  exact h

/-- Under the i.i.d. weight, each coordinate has law `p`. -/
lemma expectation_pi_eval {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι] {p : α → ℝ}
    (hp : ∑ a, p a = 1) (i : ι) (f : α → ℝ) :
    expectation (fun ω : ι → α => ∏ k, p (ω k)) (fun ω => f (ω i)) = expectation p f := by
  have h := expectation_pi_prod p fun k a => if k = i then f a else 1
  rw [Fintype.prod_eq_single i fun k hk => by simp [hk, expectation_const hp]] at h
  simpa [Fintype.prod_ite_eq'] using h

/-- Under the i.i.d. weight, the expectation of a product of functions of two distinct
coordinates factors: `E[f (ω i) g (ω j)] = E[f] E[g]` for `i ≠ j`. -/
lemma expectation_pi_eval_mul_eval {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {p : α → ℝ} (hp : ∑ a, p a = 1) {i j : ι} (hij : i ≠ j) (f g : α → ℝ) :
    expectation (fun ω : ι → α => ∏ k, p (ω k)) (fun ω => f (ω i) * g (ω j)) =
      expectation p f * expectation p g := by
  have h := expectation_pi_prod p fun k a => if k = i then f a else if k = j then g a else 1
  have hL : ∀ ω : ι → α,
      (∏ k, if k = i then f (ω k) else if k = j then g (ω k) else 1) = f (ω i) * g (ω j) := by
    intro ω
    rw [Fintype.prod_eq_mul i j hij fun k hk => by simp [hk.1, hk.2]]
    simp [hij.symm]
  have hR : (∏ k, expectation p fun a => if k = i then f a else if k = j then g a else 1) =
      expectation p f * expectation p g := by
    rw [Fintype.prod_eq_mul i j hij fun k hk => by simp [hk.1, hk.2, expectation_const hp]]
    simp [hij.symm]
  simp only [hL] at h
  rw [h, hR]

/-- The expectation of the sample mean of an i.i.d. sample is the population mean. -/
lemma expectation_sampleMean {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {p : α → ℝ} (hp : ∑ a, p a = 1) (X : α → ℝ) :
    expectation (fun ω : ι → α => ∏ i, p (ω i)) (fun ω => sampleMean fun i => X (ω i)) =
      expectation p X := by
  simp only [sampleMean_eq_sum_div, div_eq_inv_mul]
  rw [expectation_const_mul, expectation_sum]
  simp only [expectation_pi_eval hp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **Bessel's correction.** Let `ω : ι → α` be an i.i.d. sample of size `n = card ι ≥ 2` from
the finite distribution `p`, so `ω` has weight `∏ i, p (ω i)`. Then the divide-by-`(n - 1)`
sample variance of the observations `X (ω i)` has expectation `Var X`. No separate finite-variance
hypothesis is needed because `α` is finite. -/
theorem expectation_sampleVarUnbiased {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {p : α → ℝ} (hp : ∑ a, p a = 1) (hn : 2 ≤ Fintype.card ι) (X : α → ℝ) :
    expectation (fun ω : ι → α => ∏ i, p (ω i)) (fun ω => sampleVarUnbiased fun i => X (ω i)) =
      variance p X := by
  have hn2 : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  have hn0 : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have hS : (fun ω : ι → α => sampleVarUnbiased fun i => X (ω i)) = fun ω =>
      ((Fintype.card ι : ℝ) - 1)⁻¹ * (∑ i, X (ω i) * X (ω i) -
        (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∑ j, X (ω i) * X (ω j)) := by
    funext ω
    rw [sampleVarUnbiased_eq_sum_div, sum_sq_sub_sampleMean, ← Finset.sum_mul_sum,
      ← card_mul_sampleMean fun i => X (ω i)]
    field_simp
  have hij : ∀ i j : ι, expectation (fun ω : ι → α => ∏ k, p (ω k)) (fun ω => X (ω i) * X (ω j)) =
      expectation p X * expectation p X + if i = j then variance p X else 0 := by
    intro i j
    by_cases h : i = j
    · subst h
      rw [expectation_pi_eval hp i fun a => X a * X a, variance_eq_sub hp]
      simp only [sq, ite_true]
      ring
    · rw [expectation_pi_eval_mul_eval hp h X X]
      simp [h]
  rw [hS, expectation_const_mul, expectation_sub, expectation_const_mul, expectation_sum,
    expectation_sum]
  simp_rw [expectation_sum, hij]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  field_simp
  ring

/-! ## G. Least squares for a line -/

/-- The centred cross-product sum `S_xy = ∑ i, (x i - x̄) * (y i - ȳ)` of paired data
(MF06.3); `sxy x x` is `S_xx`. Mathlib has no finite-sample regression statistics. -/
noncomputable def sxy {ι : Type*} [Fintype ι] (x y : ι → ℝ) : ℝ :=
  ∑ i, (x i - sampleMean x) * (y i - sampleMean y)

/-- The least-squares slope `S_xy / S_xx` of `y` on `x` (MF06.3). With Lean's convention
`S_xy / 0 = 0` it is `0` when `S_xx = 0`, where the slope is not identified
(`ols_unique_minimizer_iff`). -/
noncomputable def olsSlope {ι : Type*} [Fintype ι] (x y : ι → ℝ) : ℝ :=
  sxy x y / sxy x x

/-- The least-squares intercept `ȳ - b̂ x̄` (MF06.3). -/
noncomputable def olsIntercept {ι : Type*} [Fintype ι] (x y : ι → ℝ) : ℝ :=
  sampleMean y - olsSlope x y * sampleMean x

/-- The residual sum of squares `∑ i, (y i - (a + b * x i)) ^ 2` of the line `a + b x`
(MF06.3). The matrix version `Cslib.MachineLearning.LeastSquares.rss` lives in `CSLibExt`, which
`MathlibExt` may not import. -/
noncomputable def rssLine {ι : Type*} [Fintype ι] (x y : ι → ℝ) (a b : ℝ) : ℝ :=
  ∑ i, (y i - (a + b * x i)) ^ 2

lemma sxy_self_eq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    sxy x x = ∑ i, (x i - sampleMean x) ^ 2 := by
  simp only [sxy, sq]

lemma sxy_self_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ sxy x x :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- `S_xy = ∑ i, x i y i - n x̄ ȳ`. -/
lemma sxy_eq_sum_mul_sub {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    sxy x y = ∑ i, x i * y i - Fintype.card ι * sampleMean x * sampleMean y := by
  have h : ∀ i, (x i - sampleMean x) * (y i - sampleMean y) =
      x i * y i - sampleMean y * x i - sampleMean x * y i + sampleMean x * sampleMean y :=
    fun i => by ring
  simp only [sxy, h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← card_mul_sampleMean x,
    ← card_mul_sampleMean y]
  ring

lemma sub_sampleMean_eq_zero_of_sxy_self_eq_zero {ι : Type*} [Fintype ι] {x : ι → ℝ}
    (h : sxy x x = 0) (i : ι) : x i - sampleMean x = 0 := by
  rw [sxy_self_eq] at h
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (x i - sampleMean x)).mp h i
    (Finset.mem_univ i)
  exact pow_eq_zero_iff two_ne_zero |>.mp this

lemma sxy_eq_zero_of_sxy_self_eq_zero {ι : Type*} [Fintype ι] {x : ι → ℝ} (h : sxy x x = 0)
    (y : ι → ℝ) : sxy x y = 0 :=
  Finset.sum_eq_zero fun i _ => by rw [sub_sampleMean_eq_zero_of_sxy_self_eq_zero h i, zero_mul]

lemma sum_resid_eq {ι : Type*} [Fintype ι] (x y : ι → ℝ) (a b : ℝ) :
    ∑ i, (y i - (a + b * x i)) =
      Fintype.card ι * (sampleMean y - a - b * sampleMean x) := by
  have h : ∀ i, y i - (a + b * x i) = y i - a - b * x i := fun i => by ring
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← card_mul_sampleMean x, ← card_mul_sampleMean y]
  ring

lemma sum_mul_resid_eq {ι : Type*} [Fintype ι] (x y : ι → ℝ) (a b : ℝ) :
    ∑ i, x i * (y i - (a + b * x i)) =
      sxy x y - b * sxy x x +
        Fintype.card ι * sampleMean x * (sampleMean y - a - b * sampleMean x) := by
  have h : ∀ i, x i * (y i - (a + b * x i)) = x i * y i - a * x i - b * (x i * x i) :=
    fun i => by ring
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, sxy_eq_sum_mul_sub,
    ← card_mul_sampleMean x]
  ring

/-- The least-squares residuals sum to zero (orthogonality to the constant vector). -/
lemma sum_resid_ols {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    ∑ i, (y i - (olsIntercept x y + olsSlope x y * x i)) = 0 := by
  rw [sum_resid_eq, olsIntercept]
  ring

/-- The least-squares residuals are orthogonal to `x`. -/
lemma sum_mul_resid_ols {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    ∑ i, x i * (y i - (olsIntercept x y + olsSlope x y * x i)) = 0 := by
  rw [sum_mul_resid_eq]
  rcases eq_or_ne (sxy x x) 0 with h | h
  · rw [h, sxy_eq_zero_of_sxy_self_eq_zero h, olsIntercept]
    ring
  · rw [olsIntercept, olsSlope, div_mul_cancel₀ _ h]
    ring

/-- **Normal equations.** If `S_xx ≠ 0`, a line `a + b x` has residuals summing to zero and
orthogonal to `x` exactly when `a` and `b` are the least-squares intercept and slope. -/
lemma normalEquations_iff {ι : Type*} [Fintype ι] {x : ι → ℝ} (hx : sxy x x ≠ 0)
    (y : ι → ℝ) (a b : ℝ) :
    (∑ i, (y i - (a + b * x i)) = 0 ∧ ∑ i, x i * (y i - (a + b * x i)) = 0) ↔
      a = olsIntercept x y ∧ b = olsSlope x y := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    intro hn
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp (by exact_mod_cast hn)
    exact hx (by simp [sxy])
  constructor
  · rintro ⟨h1, h2⟩
    rw [sum_resid_eq] at h1
    have ha : sampleMean y - a - b * sampleMean x = 0 :=
      (mul_eq_zero.mp h1).resolve_left hn
    rw [sum_mul_resid_eq, ha, mul_zero, add_zero] at h2
    have hb : b = olsSlope x y := by
      rw [olsSlope, eq_div_iff hx]
      linarith
    refine ⟨?_, hb⟩
    rw [olsIntercept, ← hb]
    linarith
  · rintro ⟨rfl, rfl⟩
    exact ⟨sum_resid_ols x y, sum_mul_resid_ols x y⟩

/-- The least-squares residuals are orthogonal to the centred regressor `x - x̄`. -/
lemma sum_sub_sampleMean_mul_resid_ols {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    ∑ i, (x i - sampleMean x) * (y i - (olsIntercept x y + olsSlope x y * x i)) = 0 := by
  rw [Finset.sum_congr rfl fun i _ => sub_mul (x i) (sampleMean x) _, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_mul_resid_ols, sum_resid_ols, mul_zero, sub_zero]

/-- Decomposition of the residual sum of squares around the least-squares line:
`RSS(a, b) = RSS(â, b̂) + n (a - â + (b - b̂) x̄) ^ 2 + (b - b̂) ^ 2 S_xx`. -/
lemma rssLine_eq_rssLine_ols_add {ι : Type*} [Fintype ι] (x y : ι → ℝ) (a b : ℝ) :
    rssLine x y a b = rssLine x y (olsIntercept x y) (olsSlope x y) +
      Fintype.card ι * (a - olsIntercept x y + (b - olsSlope x y) * sampleMean x) ^ 2 +
        (b - olsSlope x y) ^ 2 * sxy x x := by
  set r : ι → ℝ := fun i => y i - (olsIntercept x y + olsSlope x y * x i) with hr_def
  set d : ι → ℝ := fun i => x i - sampleMean x with hd_def
  have hr : ∑ i, r i = 0 := sum_resid_ols x y
  have hd : ∑ i, d i = 0 := sum_sub_sampleMean x
  have hdr : ∑ i, d i * r i = 0 := sum_sub_sampleMean_mul_resid_ols x y
  have hrss : rssLine x y (olsIntercept x y) (olsSlope x y) = ∑ i, r i ^ 2 := rfl
  have hsxx : sxy x x = ∑ i, d i * d i := rfl
  have h1 : ∀ i, (y i - (a + b * x i)) ^ 2 =
      r i ^ 2 + (a - olsIntercept x y + (b - olsSlope x y) * sampleMean x) ^ 2 +
        (b - olsSlope x y) ^ 2 * (d i * d i) -
        2 * (a - olsIntercept x y + (b - olsSlope x y) * sampleMean x) * r i -
        2 * (b - olsSlope x y) * (d i * r i) +
        2 * (a - olsIntercept x y + (b - olsSlope x y) * sampleMean x) *
          (b - olsSlope x y) * d i := by
    intro i
    simp only [hr_def, hd_def]
    ring
  have h2 : rssLine x y a b = ∑ i, r i ^ 2 +
      Fintype.card ι * (a - olsIntercept x y + (b - olsSlope x y) * sampleMean x) ^ 2 +
        (b - olsSlope x y) ^ 2 * ∑ i, d i * d i -
        2 * (a - olsIntercept x y + (b - olsSlope x y) * sampleMean x) * ∑ i, r i -
        2 * (b - olsSlope x y) * ∑ i, d i * r i +
        2 * (a - olsIntercept x y + (b - olsSlope x y) * sampleMean x) *
          (b - olsSlope x y) * ∑ i, d i := by
    simp only [rssLine, h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [h2, hr, hd, hdr, hrss, hsxx]
  ring

/-- The least-squares line minimizes the residual sum of squares (for all data). -/
lemma rssLine_ols_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) (a b : ℝ) :
    rssLine x y (olsIntercept x y) (olsSlope x y) ≤ rssLine x y a b := by
  rw [rssLine_eq_rssLine_ols_add x y a b]
  have h1 : 0 ≤ (Fintype.card ι : ℝ) *
      (a - olsIntercept x y + (b - olsSlope x y) * sampleMean x) ^ 2 := by positivity
  have h2 : 0 ≤ (b - olsSlope x y) ^ 2 * sxy x x :=
    mul_nonneg (sq_nonneg _) (sxy_self_nonneg x)
  linarith

/-- If `S_xx = 0`, so `x` is constant, adding `c` to the slope and `-c x̄` to the intercept does
not change the fitted values, so the minimizer is not unique. -/
lemma rssLine_shift_eq_of_sxy_self_eq_zero {ι : Type*} [Fintype ι] {x : ι → ℝ}
    (h : sxy x x = 0) (y : ι → ℝ) (a b c : ℝ) :
    rssLine x y (a - c * sampleMean x) (b + c) = rssLine x y a b := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := sub_sampleMean_eq_zero_of_sxy_self_eq_zero h i
  have hx : x i = sampleMean x := by linarith
  rw [hx]
  ring

/-- **Unique least-squares line.** The least-squares intercept and slope minimize the residual
sum of squares, and every minimizer equals them, if and only if `0 < S_xx`. -/
lemma ols_unique_minimizer_iff {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    (∀ a b, rssLine x y (olsIntercept x y) (olsSlope x y) ≤ rssLine x y a b ∧
      (rssLine x y a b ≤ rssLine x y (olsIntercept x y) (olsSlope x y) →
        a = olsIntercept x y ∧ b = olsSlope x y)) ↔ 0 < sxy x x := by
  constructor
  · intro h
    by_contra hneg
    have h0 : sxy x x = 0 := le_antisymm (not_lt.mp hneg) (sxy_self_nonneg x)
    have hshift := rssLine_shift_eq_of_sxy_self_eq_zero h0 y (olsIntercept x y)
      (olsSlope x y) 1
    have := ((h (olsIntercept x y - 1 * sampleMean x) (olsSlope x y + 1)).2 hshift.le).2
    linarith
  · intro hpos a b
    refine ⟨rssLine_ols_le x y a b, fun hle => ?_⟩
    rw [rssLine_eq_rssLine_ols_add x y a b] at hle
    have hn : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
    have h1 : 0 ≤ (Fintype.card ι : ℝ) *
        (a - olsIntercept x y + (b - olsSlope x y) * sampleMean x) ^ 2 := by positivity
    have h2 : (b - olsSlope x y) ^ 2 * sxy x x = 0 := by
      have : 0 ≤ (b - olsSlope x y) ^ 2 * sxy x x := by positivity
      linarith
    have hb : b = olsSlope x y := by
      have := (mul_eq_zero.mp h2).resolve_right hpos.ne'
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    have hne : (Fintype.card ι : ℝ) ≠ 0 := by
      intro hc
      have : IsEmpty ι := Fintype.card_eq_zero_iff.mp (by exact_mod_cast hc)
      simp [sxy] at hpos
    have h3 : (Fintype.card ι : ℝ) *
        (a - olsIntercept x y + (b - olsSlope x y) * sampleMean x) ^ 2 = 0 := by linarith
    have ha := (mul_eq_zero.mp h3).resolve_left hne
    rw [hb, sub_self, zero_mul, add_zero] at ha
    exact ⟨sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp ha), hb⟩

/-! ## H. Least squares in matrix form

The canonical factored form of the normal equations for a design with `Fin m` rows is
`Cslib.MachineLearning.LeastSquares.normal_inv`: `Xᵀ (X ((Xᵀ X)⁻¹ Xᵀ y)) = Xᵀ y` when
`IsUnit (Xᵀ * X).det`, with `rss_le_iff_normal` and `normal_iff` beside it. Since `CSLibExt`
depends on `MathlibExt`, this file does not import it. The Gram-form lemmas below,
`(Xᵀ X) β = Xᵀ y` for ATLAS's `olsEstimator` and general finite row and column types, are the
restatement used by the bridge `olsEstimator_designMatrix` to the line of section G. -/

open MathlibExt.Probability.Statistics.LinearModel in
/-- **Normal equations, matrix form.** If `Xᵀ X` is invertible, ATLAS's least-squares estimator
`olsEstimator X y = (Xᵀ X)⁻¹ Xᵀ y` solves `Xᵀ X β = Xᵀ y`. -/
lemma gram_mulVec_olsEstimator {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {X : Matrix m k ℝ} (hX : IsUnit (Xᵀ * X)) (y : m → ℝ) :
    (Xᵀ * X) *ᵥ olsEstimator X y = Xᵀ *ᵥ y := by
  rw [olsEstimator, olsMatrix_eq, mulVec_mulVec, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hX), Matrix.one_mul]

open MathlibExt.Probability.Statistics.LinearModel in
/-- **Uniqueness under full rank.** If `Xᵀ X` is invertible, `olsEstimator X y` is the only
solution of the normal equations `Xᵀ X β = Xᵀ y`. -/
lemma eq_olsEstimator_iff {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    {X : Matrix m k ℝ} (hX : IsUnit (Xᵀ * X)) (y : m → ℝ) (β : k → ℝ) :
    (Xᵀ * X) *ᵥ β = Xᵀ *ᵥ y ↔ β = olsEstimator X y := by
  refine ⟨fun h => Matrix.mulVec_injective_iff_isUnit.mpr hX ?_,
    fun h => h ▸ gram_mulVec_olsEstimator hX y⟩
  rw [h, gram_mulVec_olsEstimator hX]

open MathlibExt.Probability.Statistics.LinearModel in
/-- The least-squares residual `y - X β̂` is orthogonal to every column of `X`. -/
lemma transpose_mulVec_sub_olsEstimator {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {X : Matrix m k ℝ} (hX : IsUnit (Xᵀ * X)) (y : m → ℝ) :
    Xᵀ *ᵥ (y - X *ᵥ olsEstimator X y) = 0 := by
  rw [mulVec_sub, mulVec_mulVec, gram_mulVec_olsEstimator hX, sub_self]

/-- Full column rank: `Xᵀ X` is invertible if and only if the columns of `X` are linearly
independent. -/
lemma isUnit_transpose_mul_self_iff {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    (X : Matrix m k ℝ) : IsUnit (Xᵀ * X) ↔ LinearIndependent ℝ X.col := by
  rw [← Matrix.mulVec_injective_iff_isUnit, ← Matrix.mulVec_injective_iff,
    ← Matrix.coe_mulVecLin, ← Matrix.coe_mulVecLin, ← LinearMap.ker_eq_bot,
    ← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_transpose_mul_self]

/-- The design matrix of the simple linear model `y i = a + b * x i + e i`, with row `i` equal
to `(1, x i)` (MF06.3). It identifies `olsIntercept` and `olsSlope` with ATLAS's matrix
estimator (`olsEstimator_designMatrix`); Mathlib has no design-matrix constructor. -/
noncomputable def designMatrix {ι : Type*} (x : ι → ℝ) : Matrix ι (Fin 2) ℝ :=
  Matrix.of fun i => ![1, x i]

lemma designMatrix_mulVec {ι : Type*} (x : ι → ℝ) (β : Fin 2 → ℝ) :
    designMatrix x *ᵥ β = fun i => β 0 + β 1 * x i := by
  funext i
  simp [designMatrix, mulVec, dotProduct, Fin.sum_univ_two]
  ring

lemma transpose_designMatrix_mulVec {ι : Type*} [Fintype ι] (x v : ι → ℝ) :
    (designMatrix x)ᵀ *ᵥ v = ![∑ i, v i, ∑ i, x i * v i] := by
  ext j
  fin_cases j <;> simp [designMatrix, mulVec, dotProduct]

/-- `det (Xᵀ X) = n S_xx` for the design matrix of the simple linear model. -/
lemma det_gram_designMatrix {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ((designMatrix x)ᵀ * designMatrix x).det = Fintype.card ι * sxy x x := by
  rw [Matrix.det_fin_two, sxy_eq_sum_mul_sub]
  simp [designMatrix, Matrix.mul_apply, Finset.card_univ, ← card_mul_sampleMean x]
  ring

/-- The design matrix of the simple linear model has full column rank iff `0 < S_xx`. -/
lemma isUnit_gram_designMatrix_iff {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    IsUnit ((designMatrix x)ᵀ * designMatrix x) ↔ 0 < sxy x x := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, det_gram_designMatrix]
  constructor
  · intro h
    exact lt_of_le_of_ne (sxy_self_nonneg x) (Ne.symm (right_ne_zero_of_mul h))
  · intro h
    refine mul_ne_zero ?_ h.ne'
    intro hc
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp (by exact_mod_cast hc)
    simp [sxy] at h

open MathlibExt.Probability.Statistics.LinearModel in
/-- For the design matrix with rows `(1, x i)` and `0 < S_xx`, ATLAS's matrix least-squares
estimator is `(olsIntercept x y, olsSlope x y)`. -/
lemma olsEstimator_designMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] {x : ι → ℝ}
    (hx : 0 < sxy x x) (y : ι → ℝ) :
    olsEstimator (designMatrix x) y = ![olsIntercept x y, olsSlope x y] := by
  have hX := (isUnit_gram_designMatrix_iff x).mpr hx
  refine ((eq_olsEstimator_iff hX y _).mp ?_).symm
  rw [← mulVec_mulVec]
  refine (sub_eq_zero.mp ?_).symm
  rw [← mulVec_sub, designMatrix_mulVec, transpose_designMatrix_mulVec]
  ext j
  fin_cases j
  · simpa using sum_resid_ols x y
  · simpa using sum_mul_resid_ols x y

/-! ## I. Intervals under a sampling model -/

/-- The interval `[t - hi * s, t - lo * s]` for a realized statistic `t`, a scale `s` and an
acceptance region `[lo, hi]` (MF06.4). For `0 < s`, the hypothesis of the lemmas below, it is the
set of parameter values `θ` whose pivot `(t - θ) / s` lies in `[lo, hi]`
(`mem_pivotInterval_iff`). It is computed from data and carries no coverage claim; a coverage
probability follows only from a hypothesis on the law of the pivot
(`measure_mem_pivotInterval`). Mathlib has no confidence-interval definition. -/
def pivotInterval (t s lo hi : ℝ) : Set ℝ :=
  Set.Icc (t - hi * s) (t - lo * s)

/-- Pivot inversion: `θ` lies in the interval exactly when its pivot lies in the acceptance
region. -/
lemma mem_pivotInterval_iff {t s lo hi θ : ℝ} (hs : 0 < s) :
    θ ∈ pivotInterval t s lo hi ↔ (t - θ) / s ∈ Set.Icc lo hi := by
  simp only [pivotInterval, Set.mem_Icc, le_div_iff₀ hs, div_le_iff₀ hs]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

open MeasureTheory ProbabilityTheory in
/-- **Coverage under a sampling model.** If, under `μ`, the pivot `(T - θ) / s` of the statistic
`T` has law `ν`, then the interval obtained by inverting it contains `θ` with probability
`ν [lo, hi]`. -/
lemma measure_mem_pivotInterval {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ν : Measure ℝ} {T : Ω → ℝ} {s lo hi θ : ℝ} (hs : 0 < s)
    (hpivot : HasLaw (fun ω => (T ω - θ) / s) ν μ) :
    μ {ω | θ ∈ pivotInterval (T ω) s lo hi} = ν (Set.Icc lo hi) := by
  have hset : {ω | θ ∈ pivotInterval (T ω) s lo hi} =
      (fun ω => (T ω - θ) / s) ⁻¹' Set.Icc lo hi := by
    ext ω
    exact mem_pivotInterval_iff hs
  rw [hset, ← hpivot.map_eq, Measure.map_apply_of_aemeasurable hpivot.aemeasurable
    measurableSet_Icc]

open MeasureTheory ProbabilityTheory in
/-- If the statistic `T` has the normal law `N(θ, v)` with variance `v = s ^ 2`, `s ≠ 0`, then
the pivot `(T - θ) / s` has the standard normal law. -/
lemma hasLaw_pivot_of_hasLaw_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T : Ω → ℝ} {θ s : ℝ} {v : NNReal} (hs : s ≠ 0) (hv : (v : ℝ) = s ^ 2)
    (hT : HasLaw T (gaussianReal θ v) μ) :
    HasLaw (fun ω => (T ω - θ) / s) (gaussianReal 0 1) μ := by
  have h := gaussianReal_div_const (gaussianReal_sub_const hT θ) s
  convert h using 2
  · simp
  · apply NNReal.eq
    rw [NNReal.coe_div, hv, NNReal.coe_one]
    exact (div_self (pow_ne_zero 2 hs)).symm

open MeasureTheory ProbabilityTheory in
/-- **Known-variance normal location model.** Let `X ω : Fin n → ℝ` be the observations, with
`0 < n`, and let `σ > 0` be known. If, under `μ`, the pivot `(x̄ - θ) / (σ / √n)` of the sample
mean has the standard normal law, then the interval `x̄ ± z σ / √n` contains `θ` with
probability `N(0, 1) [-z, z]`. The normal law of the pivot is a hypothesis;
`hasLaw_pivot_of_hasLaw_gaussianReal` derives it from `x̄ ∼ N(θ, σ ^ 2 / n)`, and the law of `x̄`
under i.i.d. normal observations is not derived here. -/
lemma measure_mem_zInterval {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (hn : 0 < n) {σ : ℝ} (hσ : 0 < σ) {θ : ℝ} {X : Ω → Fin n → ℝ}
    (hpivot : HasLaw (fun ω => (sampleMean (X ω) - θ) / (σ / √n)) (gaussianReal 0 1) μ)
    (z : ℝ) :
    μ {ω | θ ∈ Set.Icc (sampleMean (X ω) - z * (σ / √n)) (sampleMean (X ω) + z * (σ / √n))} =
      gaussianReal 0 1 (Set.Icc (-z) z) := by
  have hs : 0 < σ / √n := div_pos hσ (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have h := measure_mem_pivotInterval (lo := -z) (hi := z) hs hpivot
  simpa [pivotInterval, sub_eq_add_neg, add_comm] using h

/-- `[lo, hi]` is a level-`c` credible interval for the real parameter `θ : Θ → ℝ` under the
posterior `post` on a finite parameter type: `post` is a finite distribution and the posterior
probability that `θ ∈ [lo, hi]` is `c` (MF06.4). This is a statement about the posterior only and
asserts no frequentist coverage. Mathlib has no credible-set notion. -/
def IsCredibleInterval {Θ : Type*} [Fintype Θ] (post θ : Θ → ℝ) (lo hi c : ℝ) : Prop :=
  (∀ t, 0 ≤ post t) ∧ ∑ t, post t = 1 ∧
    prob post (univ.filter fun t => θ t ∈ Set.Icc lo hi) = c

/-- Coverage of a credible interval under the posterior is definitional: the posterior
expectation of the indicator of `θ ∈ [lo, hi]` is the level. -/
lemma IsCredibleInterval.expectation_indicator_eq {Θ : Type*} [Fintype Θ] {post θ : Θ → ℝ}
    {lo hi c : ℝ} (h : IsCredibleInterval post θ lo hi c) :
    expectation post (fun t => if θ t ∈ Set.Icc lo hi then 1 else 0) = c := by
  rw [expectation_indicator]
  exact h.2.2

end MathlibExt.Probability.FiniteProbability
