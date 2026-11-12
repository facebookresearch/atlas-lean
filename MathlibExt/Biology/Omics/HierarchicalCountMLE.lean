/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Omics.HierarchicalCount

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Maximum marginal likelihood for the Gamma–Poisson hierarchy

`MathlibExt.Biology.Omics.HierarchicalCount` models a count `k` with size factor `s > 0` as
`k ∣ λ ~ Po(s λ)`, `λ ~ Gamma(a, b)`, so that `k` has the negative binomial marginal law
`marginalLik a b s = NB(a, s a / b)`, and estimates the hyperparameters `(a, b)` by the method of
moments. This file estimates them instead by maximizing the marginal (negative binomial) likelihood
of independent counts `k₁, …, kₙ` with size factors `s₁, …, sₙ`, each with its own rate
`λᵢ ~ Gamma(a, b)` (type-II maximum likelihood, the empirical-Bayes choice of Robbins 1956 and
Morris 1983), and compares the result with the moment estimator.

## Main definitions

* `logMarginalLik a b s k = ∑ᵢ log (marginalLik a b sᵢ kᵢ)`: the log marginal likelihood.
* `digammaIncrement a k = ∑_{j<k} 1 / (a + j)` (`= ψ(a + k) - ψ(a)`).
* `shapeScore`, `rateScore`: the partial derivatives of `logMarginalLik` in `a` and `b`;
  `rateScoreLog = b · rateScore`, the derivative in `log b`.
* `countMean k`, `countVar k`: the sample mean `M` and biased sample variance `V`;
  `profileShapeScore a k`: the shape score along the rate root `b̂(a) = σ a / M` at a common size
  factor `σ`.
* `popProfileShapeScore μ K a = E[∑_{j<K} 1 / (a + j)] - (log (a + E K) - log a)`.

## Main results

* Score equations: `log_marginalLik_eq`, `logMarginalLik_eq` (closed form);
  `hasDerivAt_logMarginalLik_shape`, `hasDerivAt_logMarginalLik_rate`.
* Concavity, in each hyperparameter separately: `concaveOn_logMarginalLik_shape`,
  `strictConcaveOn_logMarginalLik_shape` (some count positive) in `a`;
  `strictConcaveOn_logMarginalLik_logRate` in `log b`. `not_concaveOn_logMarginalLik`: the
  likelihood is not jointly concave in `(a, b)`; the tests also show it is not concave in `b`.
* Conditional estimates: at a fixed shape the rate root exists iff some count is positive
  (`exists_rateScore_eq_zero`, `rateScore_pos_of_counts_eq_zero`), is unique
  (`rateScore_eq_zero_unique`) and is the global maximizer
  (`logMarginalLik_lt_of_rateScore_eq_zero`); at a fixed rate the shape root exists and is unique
  when some count is positive (`exists_shapeScore_eq_zero`, `shapeScore_eq_zero_unique`).
* Fisher consistency of the rate equation: `hasSum_rateScore_term_mul_marginalLik`.
* Comparison with moments (common size factor `σ`): the rate root is `σ a / M`
  (`rateScore_const_eq_zero_iff`, `rateScore_const_eq_zero`); the joint score equations reduce to
  the profile shape score (`score_eq_zero_iff_const`); the moment estimates solve the rate score
  equation (`rateScore_mom_eq_zero`) and every rate root has the moment plug-in prior mean
  `M / σ` (`div_eq_mom_of_rateScore_eq_zero`). The shape equations differ: the tests exhibit a
  sample whose moment shape is not a root of the profile shape score.
  `exists_score_root_of_overdispersed`: under overdispersion `0 < M < V`, the condition for
  positive moment estimates, the score equations have a positive solution.
* Consistency: `ae_tendsto_rateMLE` (rate MLE at a known shape, strongly consistent) and
  `ae_eventually_exists_score_root` (Cramér: a strongly consistent sequence of roots of the joint
  score equations, under local identifiability of the shape). The tests instantiate its
  hypotheses for a two-point count law, which is not negative binomial.

## Not proved here

* The shape identity `E[∑_{j<K} 1 / (a + j)] = log (1 + s / b)` for `K ~ marginalLik a b s` (the
  expected shape score vanishes at the truth) and positivity of the profile information. They are
  what make the sign hypothesis of `ae_eventually_exists_score_root` true for negative binomial
  counts; here that hypothesis is assumed, not derived.
* The joint MLE as a global maximizer. The likelihood is not jointly concave; the classical
  result (a finite joint MLE exists iff the biased sample variance exceeds the sample mean, and it
  is then unique; conjectured by Anscombe 1950, proved by Aragón, Eberly and Eberly 1992) is
  formalized only in part: overdispersion gives a solution of the score equations
  (`exists_score_root_of_overdispersed`), but neither its uniqueness, nor that it maximizes the
  likelihood, nor the converse is proved. The consistency theorem accordingly gives a consistent
  root, not consistency of a unique global maximizer.
* Consistency with heterogeneous size factors, and asymptotic normality or efficiency of the MLE
  relative to the moment estimator.

## Implementation notes

The count law of a random variable is not formalized (as in `HierarchicalCount`): the consistency
theorems take i.i.d. counts and the marginal mean as hypotheses, and the mean is the proved mean of
`marginalLik` (`marginalLik_eq_negBinomialReal`, `ProbabilityTheory.hasSum_mul_negBinomialReal`).

Reuse (search of `MathlibExt` on 2026-11-12 for marginal likelihood, negative binomial MLE,
digamma, score and concavity): `MathlibExt.Probability.Statistics.GLM.NegativeBinomialDispersion`
has the per-count negative binomial log mass function and score in the (shape, log-mean)
parametrization of a regression, which is not this file's (shape, prior rate) parametrization, and
it records the same failure of joint concavity; this file works directly from
`marginalLik_eq` instead of importing that regression file. The strong law is Mathlib's
`ProbabilityTheory.strong_law_ae`; the convexity-from-derivative criteria are Mathlib's.

## References

* F. J. Anscombe, *Sampling theory of the negative binomial and logarithmic series
  distributions*, Biometrika 37 (1950), 358–382.
* J. Aragón, D. Eberly and S. Eberly, *Existence and uniqueness of the maximum likelihood
  estimator for the two-parameter negative binomial distribution*, Statist. Probab. Lett. 15
  (1992), 375–379.
* H. Cramér, *Mathematical Methods of Statistics*, Princeton University Press, 1946.
* H. Robbins, *An empirical Bayes approach to statistics*, Proc. Third Berkeley Symp. Math.
  Statist. Prob. 1 (1956), 157–163.
* C. N. Morris, *Parametric empirical Bayes inference: theory and applications*, J. Amer.
  Statist. Assoc. 78 (1983), 47–55.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology Finset Function
open scoped Nat

namespace MathlibExt.Biology.Omics.HierarchicalCount

variable {ι : Type*} [Fintype ι]

/-- The log marginal likelihood of hyperparameters `(a, b)` (prior shape and rate) for counts
`kᵢ` observed at size factors `sᵢ`, one independent rate `λᵢ ~ Gamma(a, b)` per observation:
`ℓ(a, b) = ∑ᵢ log P(kᵢ ∣ a, b, sᵢ)`, with
`P(k ∣ a, b, s) = marginalLik a b s k = NB(a, s a / b)`. -/
noncomputable def logMarginalLik (a b : ℝ) (s : ι → ℝ) (k : ι → ℕ) : ℝ :=
  ∑ i, log (marginalLik a b (s i) (k i))

/-- The digamma increment `∑_{j<k} 1 / (a + j)`, equal to `ψ(a + k) - ψ(a)` for `a > 0`; it is the
derivative in `a` of `log (a (a + 1) ⋯ (a + k - 1))`. -/
noncomputable def digammaIncrement (a : ℝ) (k : ℕ) : ℝ := ∑ j ∈ range k, (a + j)⁻¹

/-- The shape score `∂ℓ/∂a = ∑ᵢ (∑_{j<kᵢ} 1 / (a + j) + log b - log (b + sᵢ))`. -/
noncomputable def shapeScore (a b : ℝ) (s : ι → ℝ) (k : ι → ℕ) : ℝ :=
  ∑ i, (digammaIncrement a (k i) + log b - log (b + s i))

/-- The rate score `∂ℓ/∂b = ∑ᵢ (a / b - (a + kᵢ) / (b + sᵢ))`. -/
noncomputable def rateScore (a b : ℝ) (s : ι → ℝ) (k : ι → ℕ) : ℝ :=
  ∑ i, (a / b - (a + k i) / (b + s i))

private lemma log_ascPochhammer_eval {a : ℝ} (ha : 0 < a) (k : ℕ) :
    log ((ascPochhammer ℝ k).eval a) = ∑ j ∈ range k, log (a + j) := by
  have h : (ascPochhammer ℝ k).eval a = ∏ j ∈ range k, (a + j) := by
    induction k with
    | zero => simp
    | succ k ih => rw [ascPochhammer_succ_eval, ih, prod_range_succ]
  rw [h, log_prod fun j _ => by positivity]

/-- Closed form of one log marginal likelihood term: for `a, b, s > 0`,
`log P(k ∣ a, b, s) = ∑_{j<k} log (a + j) + k log s - log k! + a log b - (a + k) log (b + s)`. -/
theorem log_marginalLik_eq {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (k : ℕ) :
    log (marginalLik a b s k) = ∑ j ∈ range k, log (a + j) + k * log s - log (k ! : ℝ) +
      a * log b - (a + k) * log (b + s) := by
  have hbs : 0 < b + s := by linarith
  have hP := ascPochhammer_pos k a ha
  rw [marginalLik_eq ha hb hs.le, log_div (by positivity) (by positivity),
    log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_ascPochhammer_eval ha, log_pow,
    log_rpow hb, log_rpow hbs]
  ring

/-- Closed form of the log marginal likelihood for `a, b > 0` and positive size factors. -/
theorem logMarginalLik_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    (k : ι → ℕ) :
    logMarginalLik a b s k = ∑ i, (∑ j ∈ range (k i), log (a + j) + k i * log (s i) -
      log ((k i)! : ℝ) + a * log b - (a + k i) * log (b + s i)) :=
  sum_congr rfl fun i _ => log_marginalLik_eq ha hb (hs i) (k i)

/-! ### Score equations -/

private lemma hasDerivAt_sum_log_add {a : ℝ} (ha : 0 < a) (k : ℕ) :
    HasDerivAt (fun x => ∑ j ∈ range k, log (x + j)) (digammaIncrement a k) a := by
  rw [digammaIncrement]
  refine HasDerivAt.fun_sum fun j _ => ?_
  have h := ((hasDerivAt_id a).add_const (j : ℝ)).log (by simp only [id]; positivity)
  simpa [one_div] using h

/-- **Shape score equation.** For `a, b > 0` and positive size factors, the log marginal
likelihood is differentiable in the shape `a` with derivative `shapeScore a b s k`. -/
theorem hasDerivAt_logMarginalLik_shape {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) (k : ι → ℕ) :
    HasDerivAt (fun x => logMarginalLik x b s k) (shapeScore a b s k) a := by
  have h : HasDerivAt (fun x => ∑ i, (∑ j ∈ range (k i), log (x + j) + k i * log (s i) -
      log ((k i)! : ℝ) + x * log b - (x + k i) * log (b + s i))) (shapeScore a b s k) a := by
    rw [shapeScore]
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h1 := ((((hasDerivAt_sum_log_add ha (k i)).add_const (k i * log (s i))).sub_const
      (log ((k i)! : ℝ))).add ((hasDerivAt_id a).mul_const (log b))).sub
      (((hasDerivAt_id a).add_const (k i : ℝ)).mul_const (log (b + s i)))
    convert h1 using 1
    · funext x; simp only [Pi.add_apply, Pi.sub_apply, id]
    · ring
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ha] with x hx using logMarginalLik_eq hx hb hs k

/-- **Rate score equation.** For `a, b > 0` and positive size factors, the log marginal
likelihood is differentiable in the rate `b` with derivative `rateScore a b s k`. -/
theorem hasDerivAt_logMarginalLik_rate {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) (k : ι → ℕ) :
    HasDerivAt (fun y => logMarginalLik a y s k) (rateScore a b s k) b := by
  have h : HasDerivAt (fun y => ∑ i, (∑ j ∈ range (k i), log (a + j) + k i * log (s i) -
      log ((k i)! : ℝ) + a * log y - (a + k i) * log (y + s i))) (rateScore a b s k) b := by
    rw [rateScore]
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hbs : b + s i ≠ 0 := by linarith [hs i]
    have h1 := (((hasDerivAt_id b).log hb.ne').const_mul a).const_add
      (∑ j ∈ range (k i), log (a + j) + k i * log (s i) - log ((k i)! : ℝ))
    have h2 := (((hasDerivAt_id b).add_const (s i)).log hbs).const_mul (a + k i)
    convert h1.sub h2 using 1
    · funext y; simp only [Pi.sub_apply, id]
    · simp only [id]; ring
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hb] with y hy using logMarginalLik_eq ha hy hs k

/-! ### Concavity in each hyperparameter -/

/-- The digamma increment is antitone in `a > 0`. -/
theorem digammaIncrement_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (k : ℕ) :
    digammaIncrement y k ≤ digammaIncrement x k :=
  sum_le_sum fun j _ => inv_anti₀ (by positivity) (by linarith)

/-- The digamma increment is strictly decreasing in `a > 0` when `k ≥ 1`. -/
theorem digammaIncrement_strictAnti {x y : ℝ} (hx : 0 < x) (hxy : x < y) {k : ℕ} (hk : 0 < k) :
    digammaIncrement y k < digammaIncrement x k :=
  sum_lt_sum (fun j _ => inv_anti₀ (by positivity) (by linarith))
    ⟨0, mem_range.2 hk, inv_strictAnti₀ (by positivity) (by simpa using hxy)⟩

/-- `0 ≤ ∑_{j<k} 1 / (a + j) ≤ k / a` for `a > 0`. -/
theorem digammaIncrement_mem_Icc {a : ℝ} (ha : 0 < a) (k : ℕ) :
    digammaIncrement a k ∈ Set.Icc 0 (k / a) := by
  refine ⟨sum_nonneg fun j _ => by positivity, ?_⟩
  calc digammaIncrement a k ≤ ∑ _j ∈ range k, a⁻¹ :=
        sum_le_sum fun j _ => inv_anti₀ ha (by simp)
    _ = k / a := by simp [div_eq_mul_inv]

private lemma shapeScore_sub (x y b : ℝ) (s : ι → ℝ) (k : ι → ℕ) :
    shapeScore y b s k - shapeScore x b s k =
      ∑ i, (digammaIncrement y (k i) - digammaIncrement x (k i)) := by
  rw [shapeScore, shapeScore, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- The shape score is antitone in `a > 0`. -/
theorem shapeScore_anti {x y b : ℝ} (hx : 0 < x) (hxy : x ≤ y) (s : ι → ℝ) (k : ι → ℕ) :
    shapeScore y b s k ≤ shapeScore x b s k := by
  have := shapeScore_sub x y b s k
  have : ∑ i, (digammaIncrement y (k i) - digammaIncrement x (k i)) ≤ 0 :=
    sum_nonpos fun i _ => sub_nonpos.2 (digammaIncrement_anti hx hxy _)
  linarith

/-- The shape score is strictly decreasing in `a > 0` as soon as one count is positive. -/
theorem shapeScore_strictAnti {x y b : ℝ} (hx : 0 < x) (hxy : x < y) (s : ι → ℝ) {k : ι → ℕ}
    (hk : ∃ i, 0 < k i) : shapeScore y b s k < shapeScore x b s k := by
  have := shapeScore_sub x y b s k
  obtain ⟨i₀, hi₀⟩ := hk
  have : ∑ i, (digammaIncrement y (k i) - digammaIncrement x (k i)) < 0 :=
    sum_neg' (fun i _ => sub_nonpos.2 (digammaIncrement_anti hx hxy.le _))
      ⟨i₀, mem_univ _, sub_neg.2 (digammaIncrement_strictAnti hx hxy hi₀)⟩
  linarith

private lemma continuousOn_logMarginalLik_shape {b : ℝ} (hb : 0 < b) {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) (k : ι → ℕ) :
    ContinuousOn (fun x => logMarginalLik x b s k) (Set.Ioi 0) := fun _ hx =>
  (hasDerivAt_logMarginalLik_shape hx hb hs k).continuousAt.continuousWithinAt

private lemma deriv_logMarginalLik_shape {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) (k : ι → ℕ) :
    deriv (fun x => logMarginalLik x b s k) a = shapeScore a b s k :=
  (hasDerivAt_logMarginalLik_shape ha hb hs k).deriv

/-- **Concavity in the shape.** For a fixed rate `b > 0` and positive size factors, the log
marginal likelihood is concave in the shape `a ∈ (0, ∞)`. -/
theorem concaveOn_logMarginalLik_shape {b : ℝ} (hb : 0 < b) {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    (k : ι → ℕ) : ConcaveOn ℝ (Set.Ioi 0) (fun x => logMarginalLik x b s k) := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Ioi 0) (continuousOn_logMarginalLik_shape hb hs k)
    ?_ ?_
  · rw [interior_Ioi]
    exact fun x hx => (hasDerivAt_logMarginalLik_shape hx hb hs k).differentiableAt
      |>.differentiableWithinAt
  · rw [interior_Ioi]
    intro x hx y hy hxy
    rw [deriv_logMarginalLik_shape hx hb hs, deriv_logMarginalLik_shape hy hb hs]
    exact shapeScore_anti hx hxy s k

/-- **Strict concavity in the shape.** If at least one count is positive, the log marginal
likelihood is strictly concave in the shape `a ∈ (0, ∞)` for every fixed rate `b > 0`. -/
theorem strictConcaveOn_logMarginalLik_shape {b : ℝ} (hb : 0 < b) {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) {k : ι → ℕ} (hk : ∃ i, 0 < k i) :
    StrictConcaveOn ℝ (Set.Ioi 0) (fun x => logMarginalLik x b s k) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0)
    (continuousOn_logMarginalLik_shape hb hs k) ?_
  rw [interior_Ioi]
  intro x hx y hy hxy
  rw [deriv_logMarginalLik_shape hx hb hs, deriv_logMarginalLik_shape hy hb hs]
  exact shapeScore_strictAnti hx hxy s hk

/-- The rate score times the rate, `b ∂ℓ/∂b = ∑ᵢ (a - (a + kᵢ) · b / (b + sᵢ))`; it has the sign
of the rate score for `b > 0` and is the derivative of `ℓ` in `log b`. -/
noncomputable def rateScoreLog (a b : ℝ) (s : ι → ℝ) (k : ι → ℕ) : ℝ :=
  ∑ i, (a - (a + k i) * (b / (b + s i)))

/-- For `b > 0`, `b · rateScore a b s k = rateScoreLog a b s k`. -/
theorem rateScore_mul_self {a b : ℝ} (hb : 0 < b) {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    (k : ι → ℕ) : rateScore a b s k * b = rateScoreLog a b s k := by
  rw [rateScore, rateScoreLog, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  have : b + s i ≠ 0 := by linarith [hs i]
  field_simp

/-- `b ∂ℓ/∂b` is strictly decreasing in the rate `b > 0` (for `a > 0`, positive size factors and
a nonempty sample). -/
theorem rateScoreLog_strictAnti {a x y : ℝ} [Nonempty ι] (ha : 0 < a) (hx : 0 < x) (hxy : x < y)
    {s : ι → ℝ} (hs : ∀ i, 0 < s i) (k : ι → ℕ) :
    rateScoreLog a y s k < rateScoreLog a x s k := by
  refine sum_lt_sum_of_nonempty univ_nonempty fun i _ => ?_
  have hsi := hs i
  have hk : 0 < a + k i := by positivity
  have : x / (x + s i) < y / (y + s i) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  nlinarith

/-- **Derivative in the log rate.** For a fixed shape `a > 0` and positive size factors,
`β ↦ ℓ(a, e^β)` has derivative `rateScoreLog a (e^β) s k`; strict concavity in `β` follows in
`strictConcaveOn_logMarginalLik_logRate`. The log marginal likelihood is not concave in `b`
itself (see the tests). -/
theorem hasDerivAt_logMarginalLik_logRate {a : ℝ} (ha : 0 < a) {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) (k : ι → ℕ) (β : ℝ) :
    HasDerivAt (fun t => logMarginalLik a (exp t) s k) (rateScoreLog a (exp β) s k) β := by
  rw [← rateScore_mul_self (exp_pos β) hs]
  exact (hasDerivAt_logMarginalLik_rate ha (exp_pos β) hs k).comp β (hasDerivAt_exp β)

/-- **Strict concavity in the log rate.** For a fixed shape `a > 0`, positive size factors and a
nonempty sample, `β ↦ ℓ(a, e^β)` is strictly concave on `ℝ`. -/
theorem strictConcaveOn_logMarginalLik_logRate {a : ℝ} [Nonempty ι] (ha : 0 < a) {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) (k : ι → ℕ) :
    StrictConcaveOn ℝ Set.univ (fun t => logMarginalLik a (exp t) s k) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv convex_univ (fun t _ =>
    (hasDerivAt_logMarginalLik_logRate ha hs k t).continuousAt.continuousWithinAt) ?_
  intro x _ y _ hxy
  rw [(hasDerivAt_logMarginalLik_logRate ha hs k x).deriv,
    (hasDerivAt_logMarginalLik_logRate ha hs k y).deriv]
  exact rateScoreLog_strictAnti ha (exp_pos x) (exp_lt_exp.2 hxy) hs k

/-! ### The shape root at a fixed rate -/

private lemma shapeScore_eq_sum_add (a b : ℝ) (s : ι → ℝ) (k : ι → ℕ) :
    shapeScore a b s k = ∑ i, digammaIncrement a (k i) + ∑ i, (log b - log (b + s i)) := by
  rw [shapeScore, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

private lemma sum_log_rate_neg {b : ℝ} [Nonempty ι] (hb : 0 < b) {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) : ∑ i, (log b - log (b + s i)) < 0 :=
  sum_neg (fun i _ => sub_neg.2 (log_lt_log hb (by linarith [hs i]))) univ_nonempty

/-- **At most one shape root.** If one count is positive, then for a fixed rate the shape score
equation has at most one positive solution. -/
theorem shapeScore_eq_zero_unique {a a' b : ℝ} (ha : 0 < a) (ha' : 0 < a') {s : ι → ℝ}
    {k : ι → ℕ} (hk : ∃ i, 0 < k i) (h : shapeScore a b s k = 0)
    (h' : shapeScore a' b s k = 0) : a = a' := by
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · linarith [shapeScore_strictAnti ha hlt s hk (b := b)]
  · exact heq
  · linarith [shapeScore_strictAnti ha' hgt s hk (b := b)]

/-- **Existence of a shape root at a fixed rate.** If one count is positive, then for every
rate `b > 0` (and positive size factors) the shape score equation has a positive solution. -/
theorem exists_shapeScore_eq_zero {b : ℝ} [Nonempty ι] (hb : 0 < b) {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) {k : ι → ℕ} (hk : ∃ i, 0 < k i) :
    ∃ a, 0 < a ∧ shapeScore a b s k = 0 := by
  set C := ∑ i, (log b - log (b + s i)) with hC
  have hC0 : C < 0 := sum_log_rate_neg hb hs
  obtain ⟨i₀, hi₀⟩ := hk
  set a₁ := 1 / (1 - C) with ha₁
  have ha₁0 : 0 < a₁ := by rw [ha₁]; apply div_pos one_pos; linarith
  have h₁ : 0 < shapeScore a₁ b s k := by
    rw [shapeScore_eq_sum_add]
    have hle : digammaIncrement a₁ (k i₀) ≤ ∑ i, digammaIncrement a₁ (k i) :=
      single_le_sum (fun i _ => (digammaIncrement_mem_Icc ha₁0 _).1) (mem_univ i₀)
    have hge : a₁⁻¹ ≤ digammaIncrement a₁ (k i₀) := by
      rw [digammaIncrement]
      have := single_le_sum (f := fun j : ℕ => (a₁ + j)⁻¹) (fun j _ => by positivity)
        (mem_range.2 hi₀)
      simpa using this
    have : a₁⁻¹ = 1 - C := by rw [ha₁, one_div, inv_inv]
    linarith
  set K := ∑ i, (k i : ℝ) with hK
  have hK0 : 0 ≤ K := sum_nonneg fun i _ => by positivity
  set a₂ := K / (-C) + 1 with ha₂
  have ha₂0 : 0 < a₂ := by rw [ha₂]; have : 0 ≤ K / (-C) := div_nonneg hK0 (by linarith); linarith
  have h₂ : shapeScore a₂ b s k < 0 := by
    rw [shapeScore_eq_sum_add]
    have hle : ∑ i, digammaIncrement a₂ (k i) ≤ K / a₂ := by
      rw [hK, sum_div]
      exact sum_le_sum fun i _ => (digammaIncrement_mem_Icc ha₂0 _).2
    have : K / a₂ < -C := by
      rw [div_lt_iff₀ ha₂0, ha₂, mul_add, mul_one, mul_div_cancel₀ _ (by linarith : -C ≠ 0)]
      linarith
    linarith
  have hlt : a₁ < a₂ := by
    by_contra hc
    linarith [shapeScore_anti ha₂0 (not_lt.1 hc) s k (b := b)]
  have hcont : ContinuousOn (fun a => shapeScore a b s k) (Set.Icc a₁ a₂) := by
    intro a ha
    have ha0 : 0 < a := lt_of_lt_of_le ha₁0 ha.1
    refine ContinuousAt.continuousWithinAt ?_
    exact tendsto_finsetSum _ fun i _ => ((tendsto_finsetSum _ fun j _ =>
      (continuousAt_id.add continuousAt_const).inv₀ (by
        have : 0 < a + (j : ℝ) := by positivity
        exact this.ne')).add continuousAt_const).sub continuousAt_const
  obtain ⟨a, ha, hroot⟩ := intermediate_value_Icc' hlt.le hcont ⟨h₂.le, h₁.le⟩
  exact ⟨a, lt_of_lt_of_le ha₁0 ha.1, hroot⟩

/-! ### The rate MLE at a fixed shape -/

/-- **At most one rate root.** For a fixed shape `a > 0`, the rate score equation has at most one
positive solution. -/
theorem rateScore_eq_zero_unique {a b b' : ℝ} [Nonempty ι] (ha : 0 < a) (hb : 0 < b)
    (hb' : 0 < b') {s : ι → ℝ} (hs : ∀ i, 0 < s i) {k : ι → ℕ} (h : rateScore a b s k = 0)
    (h' : rateScore a b' s k = 0) : b = b' := by
  have e := rateScore_mul_self (a := a) hb hs k
  have e' := rateScore_mul_self (a := a) hb' hs k
  rw [h, zero_mul] at e
  rw [h', zero_mul] at e'
  rcases lt_trichotomy b b' with hlt | heq | hgt
  · linarith [rateScoreLog_strictAnti ha hb hlt hs k]
  · exact heq
  · linarith [rateScoreLog_strictAnti ha hb' hgt hs k]

/-- **All-zero counts: no rate root.** If every count is `0`, the rate score is strictly positive
at every `b > 0`, so the log marginal likelihood increases in `b` without a critical point. -/
theorem rateScore_pos_of_counts_eq_zero {a b : ℝ} [Nonempty ι] (ha : 0 < a) (hb : 0 < b)
    {s : ι → ℝ} (hs : ∀ i, 0 < s i) {k : ι → ℕ} (hk : ∀ i, k i = 0) : 0 < rateScore a b s k := by
  refine sum_pos (fun i _ => ?_) univ_nonempty
  have hsi := hs i
  rw [hk i, Nat.cast_zero, add_zero, sub_pos]
  exact div_lt_div_of_pos_left ha hb (by linarith)

private lemma rateScoreLog_eq {a b : ℝ} (hb : 0 ≤ b) {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    (k : ι → ℕ) :
    rateScoreLog a b s k = -∑ i, (k i : ℝ) + ∑ i, (a + k i) * s i / (b + s i) := by
  rw [rateScoreLog, neg_eq_neg_one_mul, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  have : b + s i ≠ 0 := by linarith [hs i]
  field_simp
  ring

private lemma continuousOn_rateScoreLog (a : ℝ) {s : ι → ℝ} (hs : ∀ i, 0 < s i) (k : ι → ℕ) :
    ContinuousOn (fun b => rateScoreLog a b s k) (Set.Ici 0) := by
  refine continuousOn_finsetSum _ fun i _ => continuousOn_const.sub (continuousOn_const.mul
    (continuousOn_id.div (continuousOn_id.add continuousOn_const) fun b hb => ?_))
  have : (0 : ℝ) ≤ b := hb
  have := hs i
  positivity

/-- **Existence of the rate MLE at a fixed shape.** If at least one count is positive, then for
every shape `a > 0` the rate score equation has a positive solution (unique by
`rateScore_eq_zero_unique`). -/
theorem exists_rateScore_eq_zero {a : ℝ} [Nonempty ι] (ha : 0 < a) {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) {k : ι → ℕ} (hk : ∃ i, 0 < k i) :
    ∃ b, 0 < b ∧ rateScore a b s k = 0 := by
  have hK : 0 < ∑ i, (k i : ℝ) := by
    obtain ⟨i₀, hi₀⟩ := hk
    exact sum_pos' (fun i _ => by positivity) ⟨i₀, mem_univ _, by exact_mod_cast hi₀⟩
  have hlim : Tendsto (fun b => -∑ i, (k i : ℝ) + ∑ i, (a + k i) * s i / (b + s i)) atTop
      (𝓝 (-∑ i, (k i : ℝ) + 0)) := by
    refine tendsto_const_nhds.add ?_
    rw [← sum_const_zero (s := (univ : Finset ι))]
    exact tendsto_finsetSum _ fun i _ =>
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ (s i) tendsto_id)
  have hneg : -∑ i, (k i : ℝ) + 0 < 0 := by linarith
  obtain ⟨B, hB, hB0⟩ := ((hlim.eventually (gt_mem_nhds hneg)).and
    (eventually_ge_atTop 0)).exists
  rw [← rateScoreLog_eq hB0 hs] at hB
  have h0 : rateScoreLog a 0 s k = Fintype.card ι * a := by simp [rateScoreLog]
  have hpos : 0 < rateScoreLog a 0 s k := by
    rw [h0]; have := Fintype.card_pos (α := ι); positivity
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hB0
    ((continuousOn_rateScoreLog a hs k).mono Set.Icc_subset_Ici_self) ⟨hB.le, hpos.le⟩
  have hc0' : c ≠ 0 := by rintro rfl; linarith
  have hcpos : 0 < c := lt_of_le_of_ne hc.1 (Ne.symm hc0')
  refine ⟨c, hcpos, ?_⟩
  have := rateScore_mul_self (a := a) hcpos hs k
  simp only at hc0
  rw [hc0] at this
  exact (mul_eq_zero.1 this).resolve_right hc0'

/-- **The rate root is the global maximizer.** For a fixed shape `a > 0`, a positive root `b̂` of
the rate score equation is the unique maximizer of `b ↦ ℓ(a, b)` over `b > 0`. -/
theorem logMarginalLik_lt_of_rateScore_eq_zero {a bhat b : ℝ} [Nonempty ι] (ha : 0 < a)
    (hbhat : 0 < bhat) (hb : 0 < b) (hne : b ≠ bhat) {s : ι → ℝ} (hs : ∀ i, 0 < s i) {k : ι → ℕ}
    (h : rateScore a bhat s k = 0) : logMarginalLik a b s k < logMarginalLik a bhat s k := by
  have hL0 : rateScoreLog a bhat s k = 0 := by rw [← rateScore_mul_self hbhat hs, h, zero_mul]
  have hderiv : ∀ x, 0 < x → deriv (fun y => logMarginalLik a y s k) x = rateScore a x s k :=
    fun x hx => (hasDerivAt_logMarginalLik_rate ha hx hs k).deriv
  have hcont : ContinuousOn (fun y => logMarginalLik a y s k) (Set.Ioi 0) := fun x hx =>
    (hasDerivAt_logMarginalLik_rate ha hx hs k).continuousAt.continuousWithinAt
  have hsign : ∀ x, 0 < x → (0 < rateScore a x s k ↔ 0 < rateScoreLog a x s k) := fun x hx => by
    rw [← rateScore_mul_self hx hs]; exact (mul_pos_iff_of_pos_right hx).symm
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmono : StrictMonoOn (fun y => logMarginalLik a y s k) (Set.Ioc 0 bhat) := by
      refine strictMonoOn_of_deriv_pos (convex_Ioc 0 bhat)
        (hcont.mono fun x hx => hx.1) fun x hx => ?_
      rw [interior_Ioc] at hx
      rw [hderiv x hx.1, hsign x hx.1]
      linarith [rateScoreLog_strictAnti ha hx.1 hx.2 hs k]
    exact hmono ⟨hb, hlt.le⟩ ⟨hbhat, le_rfl⟩ hlt
  · have hanti : StrictAntiOn (fun y => logMarginalLik a y s k) (Set.Ici bhat) := by
      refine strictAntiOn_of_deriv_neg (convex_Ici bhat)
        (hcont.mono fun x hx => lt_of_lt_of_le hbhat hx) fun x hx => ?_
      rw [interior_Ici] at hx
      have hx0 : 0 < x := lt_trans hbhat hx
      rw [hderiv x hx0]
      have : rateScoreLog a x s k < 0 := by linarith [rateScoreLog_strictAnti ha hbhat hx hs k]
      have e := rateScore_mul_self (a := a) hx0 hs k
      nlinarith
    exact hanti le_rfl hgt.le hgt

/-! ### A common size factor: profile likelihood and comparison with moments -/

/-- The sample mean `M = (∑ᵢ kᵢ) / n` of a finite sample of `n` counts. -/
noncomputable def countMean (k : ι → ℕ) : ℝ := (∑ i, (k i : ℝ)) / Fintype.card ι

/-- The rate score at a common size factor `σ`: `n a / b - (n a + ∑ᵢ kᵢ) / (b + σ)`. -/
theorem rateScore_const (a b σ : ℝ) (k : ι → ℕ) :
    rateScore a b (fun _ => σ) k =
      Fintype.card ι * a / b - (Fintype.card ι * a + ∑ i, (k i : ℝ)) / (b + σ) := by
  simp only [rateScore, sum_sub_distrib, ← sum_div, sum_add_distrib, sum_const, card_univ,
    nsmul_eq_mul]

/-- **Rate score equation at a common size factor.** For `a, b, σ > 0`, the rate score vanishes
iff `b M = σ a`, i.e. iff the fitted marginal mean `σ a / b` equals the sample mean `M`. -/
theorem rateScore_const_eq_zero_iff {a b σ : ℝ} [Nonempty ι] (hb : 0 < b) (hσ : 0 < σ)
    (k : ι → ℕ) : rateScore a b (fun _ => σ) k = 0 ↔ b * countMean k = σ * a := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hbσ : 0 < b + σ := by linarith
  rw [rateScore_const, countMean, sub_eq_zero, div_eq_div_iff hb.ne' hbσ.ne']
  constructor <;> intro h
  · field_simp; nlinarith
  · field_simp at h; nlinarith

/-- **The rate MLE matches the sample mean.** At a common size factor `σ > 0` and a positive
sample mean `M`, the rate root at shape `a > 0` is `b̂(a) = σ a / M`. -/
theorem rateScore_const_eq_zero {a σ : ℝ} [Nonempty ι] (ha : 0 < a) (hσ : 0 < σ) {k : ι → ℕ}
    (hM : 0 < countMean k) : rateScore a (σ * a / countMean k) (fun _ => σ) k = 0 := by
  rw [rateScore_const_eq_zero_iff (a := a) (by positivity) hσ]
  field_simp

/-- The moment rate estimate is `σ â / M` at the moment shape estimate `â = momShape M V`. -/
theorem momRate_eq_mul_momShape_div {σ M V : ℝ} (hM : M ≠ 0) :
    momRate σ M V = σ * momShape M V / M := by
  rw [momRate, momShape]; field_simp

/-- **Method of moments solves the rate score equation.** At a common size factor `σ > 0`, if
the sample is overdispersed (`0 < M < V`, with `M` the sample mean), the moment estimates
`(momShape M V, momRate σ M V)` solve the rate score equation of the marginal likelihood exactly.
They do not solve the shape score equation in general (see the tests). -/
theorem rateScore_mom_eq_zero {σ V : ℝ} [Nonempty ι] (hσ : 0 < σ) {k : ι → ℕ}
    (hM : 0 < countMean k) (hMV : countMean k < V) :
    rateScore (momShape (countMean k) V) (momRate σ (countMean k) V) (fun _ => σ) k = 0 := by
  have hVM : 0 < V - countMean k := by linarith
  have ha : 0 < momShape (countMean k) V := div_pos (by positivity) hVM
  rw [momRate_eq_mul_momShape_div hM.ne']
  exact rateScore_const_eq_zero ha hσ hM

/-- The profile shape score at a common size factor: the shape score along the rate root
`b̂(a) = σ a / M`, `∑ᵢ ∑_{j<kᵢ} 1 / (a + j) - n (log (a + M) - log a)`. It does not depend on
`σ`. -/
noncomputable def profileShapeScore (a : ℝ) (k : ι → ℕ) : ℝ :=
  ∑ i, digammaIncrement a (k i) - Fintype.card ι * (log (a + countMean k) - log a)

/-- Along the rate root `b̂(a) = σ a / M`, the shape score is the profile shape score. -/
theorem shapeScore_const_rateRoot {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) {k : ι → ℕ}
    (hM : 0 < countMean k) :
    shapeScore a (σ * a / countMean k) (fun _ => σ) k = profileShapeScore a k := by
  have hb : 0 < σ * a / countMean k := by positivity
  have hlog : log (σ * a / countMean k) - log (σ * a / countMean k + σ) =
      -(log (a + countMean k) - log a) := by
    have : σ * a / countMean k + σ = σ * (a + countMean k) / countMean k := by field_simp
    rw [this, log_div (by positivity) hM.ne', log_div (by positivity) hM.ne',
      log_mul hσ.ne' ha.ne', log_mul hσ.ne' (by positivity)]
    ring
  simp only [shapeScore, profileShapeScore, add_sub_assoc, sum_add_distrib, hlog, sum_neg_distrib,
    sum_const, card_univ, nsmul_eq_mul]
  ring

/-- **Joint score equations at a common size factor.** For `a, b, σ > 0` and a positive sample
mean, `(a, b)` solves both score equations iff `b = σ a / M` and `a` is a root of the profile
shape score. -/
theorem score_eq_zero_iff_const {a b σ : ℝ} [Nonempty ι] (ha : 0 < a) (hb : 0 < b) (hσ : 0 < σ)
    {k : ι → ℕ} (hM : 0 < countMean k) :
    (shapeScore a b (fun _ => σ) k = 0 ∧ rateScore a b (fun _ => σ) k = 0) ↔
      (b = σ * a / countMean k ∧ profileShapeScore a k = 0) := by
  constructor
  · rintro ⟨hs, hr⟩
    have hb' : b = σ * a / countMean k := by
      rw [rateScore_const_eq_zero_iff hb hσ] at hr
      field_simp; linarith
    refine ⟨hb', ?_⟩
    rw [← shapeScore_const_rateRoot ha hσ hM, ← hb', hs]
  · rintro ⟨rfl, hp⟩
    exact ⟨by rw [shapeScore_const_rateRoot ha hσ hM, hp], rateScore_const_eq_zero ha hσ hM⟩

/-- **Every root of the rate equation shares the moment fitted mean.** At a common size factor
`σ > 0`, every solution `(a, b)` of the rate score equation has plug-in prior mean
`a / b = M / σ`, which is also the moment plug-in prior mean `momShape M V / momRate σ M V` for
any `V > M`. The two sets of estimating equations differ only in the shape equation: a root of the
score equations solves `∑ᵢ ∑_{j<kᵢ} 1 / (a + j) = n log (1 + M / a)`, the moment estimator
`M + M² / a = V`. -/
theorem div_eq_mom_of_rateScore_eq_zero {a b σ V : ℝ} [Nonempty ι] (hb : 0 < b) (hσ : 0 < σ)
    {k : ι → ℕ} (hM : 0 < countMean k) (hMV : countMean k < V)
    (h : rateScore a b (fun _ => σ) k = 0) :
    a / b = countMean k / σ ∧
      momShape (countMean k) V / momRate σ (countMean k) V = countMean k / σ := by
  rw [rateScore_const_eq_zero_iff hb hσ] at h
  have hVM : 0 < V - countMean k := by linarith
  refine ⟨?_, ?_⟩
  · field_simp; linarith
  · rw [momShape, momRate]; field_simp

/-- **The rate score is unbiased.** Under the hierarchy's own marginal law
`marginalLik a b s = NB(a, s a / b)`, one count's rate score `a / b - (a + k) / (b + s)` has mean
`0`: the rate score equation is Fisher consistent. -/
theorem hasSum_rateScore_term_mul_marginalLik {a b s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 ≤ s) :
    HasSum (fun k : ℕ => (a / b - (a + k) / (b + s)) * marginalLik a b s k) 0 := by
  have hμ : 0 ≤ s * a / b := by positivity
  have h1 := hasSum_negBinomialReal ha hμ
  have h2 := hasSum_mul_negBinomialReal ha hμ
  have hbs : 0 < b + s := by linarith
  have h := ((h1.mul_left (a / b - a / (b + s))).sub (h2.mul_left (1 / (b + s))))
  have hval : (a / b - a / (b + s)) * 1 - 1 / (b + s) * (s * a / b) = 0 := by
    field_simp; ring
  rw [hval] at h
  refine h.congr_fun fun k => ?_
  rw [marginalLik_eq_negBinomialReal ha hb hs]
  ring

/-- **The log marginal likelihood is not jointly concave.** For one zero count at size factor
`1`, `ℓ(a, b) = a log (b / (b + 1))` violates midpoint concavity between `(1, 1)` and `(3, 3)`:
`ℓ(2, 2) < (ℓ(1, 1) + ℓ(3, 3)) / 2`, because `2¹¹ < 3⁷`. Concavity holds only in each
hyperparameter separately (`concaveOn_logMarginalLik_shape`,
`strictConcaveOn_logMarginalLik_logRate`). -/
theorem not_concaveOn_logMarginalLik :
    ¬ ConcaveOn ℝ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
      (fun p : ℝ × ℝ => logMarginalLik p.1 p.2 (fun _ : Unit => (1 : ℝ)) (fun _ => 0)) := by
  intro h
  have hmem : ∀ x : ℝ, 0 < x → (x, x) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) :=
    fun x hx => ⟨hx, hx⟩
  have hc := h.2 (hmem 1 one_pos) (hmem 3 (by norm_num)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hpt : ((1 / 2 : ℝ) • ((1 : ℝ), (1 : ℝ)) + (1 / 2 : ℝ) • ((3 : ℝ), (3 : ℝ))) =
      ((2 : ℝ), (2 : ℝ)) := by
    ext <;> simp <;> norm_num
  rw [hpt] at hc
  have hf : ∀ x : ℝ, 0 < x → logMarginalLik x x (fun _ : Unit => (1 : ℝ)) (fun _ => 0) =
      x * log x - x * log (x + 1) := fun x hx => by
    rw [logMarginalLik_eq hx hx (fun _ => one_pos)]
    simp
  simp only [smul_eq_mul, hf 1 one_pos, hf 2 two_pos, hf 3 (by norm_num : (0 : ℝ) < 3)] at hc
  have h2 : (2 : ℝ) ^ 11 < 3 ^ 7 := by norm_num
  have hlog := log_lt_log (by positivity) h2
  rw [log_pow, log_pow] at hlog
  have h4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
  norm_num [log_one, h4] at hc
  push_cast at hlog
  linarith

/-! ### Consistency -/

/-- The population profile shape score of a count random variable `K`:
`E[∑_{j<K} 1 / (a + j)] - (log (a + E K) - log a)`. It is the almost sure limit of
`n⁻¹ · profileShapeScore a (K₁, …, Kₙ)` for i.i.d. copies `Kᵢ` of `K`. -/
noncomputable def popProfileShapeScore {Ω : Type*} {_ : MeasurableSpace Ω} (μ : Measure Ω)
    (K : Ω → ℕ) (a : ℝ) : ℝ :=
  μ[fun ω => digammaIncrement a (K ω)] - (log (a + μ[fun ω => (K ω : ℝ)]) - log a)

private lemma inv_card_mul_profileShapeScore {a : ℝ} [Nonempty ι] (k : ι → ℕ) :
    (Fintype.card ι : ℝ)⁻¹ * profileShapeScore a k =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, digammaIncrement a (k i) -
        (log (a + countMean k) - log a) := by
  have : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [profileShapeScore]; field_simp

private lemma continuousOn_profileShapeScore (k : ι → ℕ) (hM : 0 ≤ countMean k) :
    ContinuousOn (fun a => profileShapeScore a k) (Set.Ioi 0) := by
  intro a ha
  have ha : (0 : ℝ) < a := ha
  refine ContinuousAt.continuousWithinAt ?_
  refine (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
    (continuousAt_id.add continuousAt_const).inv₀ (by
      have : 0 < a + (j : ℝ) := by positivity
      exact this.ne')).sub
    (continuousAt_const.mul (((continuousAt_id.add continuousAt_const).log
      (add_pos_of_pos_of_nonneg ha hM).ne').sub (continuousAt_id.log ha.ne')))

/-! ### Overdispersion gives a solution of the score equations -/

/-- The biased (divisor `n`) sample variance `V = n⁻¹ ∑ᵢ kᵢ² - M²` of a finite sample of counts. -/
noncomputable def countVar (k : ι → ℕ) : ℝ :=
  (∑ i, (k i : ℝ) ^ 2) / Fintype.card ι - countMean k ^ 2

private lemma log_one_add_ge {x : ℝ} (hx : 0 ≤ x) : x - x ^ 2 / 2 ≤ log (1 + x) := by
  have hmono : MonotoneOn (fun y => log (1 + y) - y + y ^ 2 / 2) (Set.Ici 0) := by
    have hd : ∀ y, 0 ≤ y → HasDerivAt (fun y => log (1 + y) - y + y ^ 2 / 2)
        ((1 + y)⁻¹ - 1 + y) y := fun y hy => by
      have h1 := ((hasDerivAt_id y).const_add 1).log (by simp only [id]; positivity)
      have h2 := (h1.sub (hasDerivAt_id y)).add ((hasDerivAt_pow 2 y).div_const 2)
      convert h2 using 1
      · funext y; simp only [Pi.add_apply, Pi.sub_apply, id]
      · simp only [id]; field_simp; ring
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt)
      fun y hy => ?_
    rw [interior_Ici] at hy
    have hy : (0 : ℝ) < y := hy
    rw [(hd y hy.le).deriv]
    have : (1 + y)⁻¹ - 1 + y = y ^ 2 / (1 + y) := by field_simp; ring
    rw [this]; positivity
  have := hmono (Set.mem_Ici.2 le_rfl) hx hx
  simp only [add_zero, log_one, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div] at this
  linarith

private lemma digammaIncrement_le_cubic {a : ℝ} (ha : 0 < a) (k : ℕ) :
    digammaIncrement a k ≤ k / a - (k * (k - 1) / 2) / a ^ 2 + (k : ℝ) ^ 3 / a ^ 3 := by
  have hterm : ∀ j : ℕ, (a + j)⁻¹ ≤ 1 / a - j / a ^ 2 + (j : ℝ) ^ 2 / a ^ 3 := fun j => by
    have hj : (0 : ℝ) ≤ j := j.cast_nonneg
    rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
    have : (1 / a - j / a ^ 2 + (j : ℝ) ^ 2 / a ^ 3) * (a + j) = 1 + (j : ℝ) ^ 3 / a ^ 3 := by
      field_simp; ring
    rw [this]
    have : 0 ≤ (j : ℝ) ^ 3 / a ^ 3 := by positivity
    linarith
  have hsum1 : ∑ j ∈ range k, (j : ℝ) = k * (k - 1) / 2 := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, ih]; push_cast; ring
  have hsum2 : ∑ j ∈ range k, (j : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by
    calc ∑ j ∈ range k, (j : ℝ) ^ 2 ≤ ∑ _j ∈ range k, (k : ℝ) ^ 2 :=
          sum_le_sum fun j hj => by
            have := mem_range.1 hj
            exact pow_le_pow_left₀ j.cast_nonneg (by exact_mod_cast this.le) 2
      _ = (k : ℝ) ^ 3 := by simp; ring
  calc digammaIncrement a k ≤ ∑ j ∈ range k, (1 / a - j / a ^ 2 + (j : ℝ) ^ 2 / a ^ 3) :=
        sum_le_sum fun j _ => hterm j
    _ = k / a - (∑ j ∈ range k, (j : ℝ)) / a ^ 2 + (∑ j ∈ range k, (j : ℝ) ^ 2) / a ^ 3 := by
        rw [sum_add_distrib, sum_sub_distrib, sum_div, sum_div]; simp [div_eq_mul_inv]
    _ ≤ k / a - (k * (k - 1) / 2) / a ^ 2 + (k : ℝ) ^ 3 / a ^ 3 := by
        rw [hsum1]; gcongr

private lemma profileShapeScore_neg {a : ℝ} [Nonempty ι] (ha : 0 < a) {k : ι → ℕ}
    (hM : 0 < countMean k) :
    profileShapeScore a k ≤
      -(Fintype.card ι * (countVar k - countMean k)) / (2 * a ^ 2) +
        (∑ i, (k i : ℝ) ^ 3) / a ^ 3 := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hlog : log (a + countMean k) - log a = log (1 + countMean k / a) := by
    rw [← log_div (by positivity) ha.ne']; congr 1; field_simp
  have hl := log_one_add_ge (x := countMean k / a) (by positivity)
  have hh : ∑ i, digammaIncrement a (k i) ≤
      ∑ i, ((k i : ℝ) / a - ((k i : ℝ) * (k i - 1) / 2) / a ^ 2 + (k i : ℝ) ^ 3 / a ^ 3) :=
    sum_le_sum fun i _ => digammaIncrement_le_cubic ha (k i)
  have hA : ∑ i, (k i : ℝ) = Fintype.card ι * countMean k := by
    rw [countMean]; field_simp
  have hB : ∑ i, (k i : ℝ) ^ 2 = Fintype.card ι * (countVar k + countMean k ^ 2) := by
    rw [countVar]; field_simp; ring
  have hh' : ∑ i, digammaIncrement a (k i) ≤ (∑ i, (k i : ℝ)) / a -
      (∑ i, (k i : ℝ) ^ 2) / (2 * a ^ 2) + (∑ i, (k i : ℝ)) / (2 * a ^ 2) +
        (∑ i, (k i : ℝ) ^ 3) / a ^ 3 := by
    refine hh.trans (le_of_eq ?_)
    rw [sum_div, sum_div, sum_div, sum_div, ← sum_sub_distrib, ← sum_add_distrib,
      ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [profileShapeScore, hlog]
  rw [hA, hB] at hh'
  have key : Fintype.card ι * countMean k / a -
      Fintype.card ι * (countVar k + countMean k ^ 2) / (2 * a ^ 2) +
        Fintype.card ι * countMean k / (2 * a ^ 2) -
          Fintype.card ι * (countMean k / a - (countMean k / a) ^ 2 / 2) =
      -(Fintype.card ι * (countVar k - countMean k)) / (2 * a ^ 2) := by
    field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left hl hn.le]

private lemma exists_profileShapeScore_pos [Nonempty ι] {k : ι → ℕ} (hM : 0 < countMean k) :
    ∃ a, 0 < a ∧ 0 < profileShapeScore a k := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, 0 < k i := by
    by_contra h
    push Not at h
    have : countMean k = 0 := by simp [countMean, fun i => Nat.le_zero.1 (h i)]
    linarith
  set n : ℝ := (Fintype.card ι : ℝ)
  set M := countMean k
  set g : ℝ → ℝ := fun x => 1 - n * (x * log (x + M) - x * log x) with hg
  have hgc : ContinuousAt g 0 := continuousAt_const.sub (continuousAt_const.mul
    ((continuousAt_id.mul ((continuousAt_id.add continuousAt_const).log
      (by simpa using hM.ne'))).sub Real.continuous_mul_log.continuousAt))
  have hg0 : (0 : ℝ) < g 0 := by simp [hg]
  obtain ⟨a, hga, ha⟩ := (((hgc.eventually (lt_mem_nhds hg0)).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  have ha : (0 : ℝ) < a := ha
  refine ⟨a, ha, ?_⟩
  have hsum : a⁻¹ ≤ ∑ i, digammaIncrement a (k i) := by
    refine le_trans ?_ (single_le_sum (fun i _ => (digammaIncrement_mem_Icc ha _).1)
      (mem_univ i₀))
    rw [digammaIncrement]
    simpa using single_le_sum (f := fun j : ℕ => (a + j)⁻¹) (fun j _ => by positivity)
      (mem_range.2 hi₀)
  have hprod : g a ≤ a * profileShapeScore a k := by
    have h1 : 1 ≤ a * ∑ i, digammaIncrement a (k i) := by
      have := mul_le_mul_of_nonneg_left hsum ha.le
      rwa [mul_inv_cancel₀ ha.ne'] at this
    rw [profileShapeScore]
    simp only [hg]
    nlinarith
  by_contra hc
  have := mul_nonpos_of_nonneg_of_nonpos ha.le (not_lt.1 hc)
  linarith

/-- **Overdispersion gives a solution of the score equations.** At a common size factor
`σ > 0`, if the sample is overdispersed, `0 < M < V` (exactly the condition under which the moment
estimates `momShape M V`, `momRate σ M V` are positive), then the score equations of the marginal
likelihood have a solution `(â, σ â / M)` with `â > 0`. Uniqueness, and that the solution is the
global maximizer, are not proved here. -/
theorem exists_score_root_of_overdispersed {σ : ℝ} [Nonempty ι] (hσ : 0 < σ) {k : ι → ℕ}
    (hM : 0 < countMean k) (hMV : countMean k < countVar k) :
    ∃ a b, 0 < a ∧ 0 < b ∧ shapeScore a b (fun _ => σ) k = 0 ∧
      rateScore a b (fun _ => σ) k = 0 := by
  obtain ⟨a₁, ha₁, hP₁⟩ := exists_profileShapeScore_pos hM
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set D : ℝ := (Fintype.card ι : ℝ) * (countVar k - countMean k) with hD
  have hD0 : 0 < D := mul_pos hn (by linarith)
  set C := ∑ i, (k i : ℝ) ^ 3 with hC
  have hC0 : 0 ≤ C := sum_nonneg fun i _ => by positivity
  set a₂ := a₁ + 2 * C / D + 1 with ha₂
  have hCD : 0 ≤ 2 * C / D := by positivity
  have ha₂0 : 0 < a₂ := by linarith
  have hlt : a₁ < a₂ := by linarith
  have hP₂ : profileShapeScore a₂ k < 0 := by
    refine lt_of_le_of_lt (profileShapeScore_neg ha₂0 hM) ?_
    rw [← hD, ← hC]
    have h2C : 2 * C < D * a₂ := by
      have : D * (2 * C / D) = 2 * C := by field_simp
      nlinarith
    have : -D / (2 * a₂ ^ 2) + C / a₂ ^ 3 = (2 * C - D * a₂) / (2 * a₂ ^ 3) := by
      field_simp; ring
    rw [this]
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  obtain ⟨a, ha, hPa⟩ := intermediate_value_Icc' hlt.le
    ((continuousOn_profileShapeScore k hM.le).mono fun x hx =>
      (lt_of_lt_of_le ha₁ hx.1 : 0 < x)) ⟨hP₂.le, hP₁.le⟩
  have ha0 : 0 < a := lt_of_lt_of_le ha₁ ha.1
  have hb : 0 < σ * a / countMean k := by positivity
  exact ⟨a, _, ha0, hb, (score_eq_zero_iff_const ha0 hb hσ hM).2 ⟨rfl, hPa⟩⟩

section Sampling

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {X : ℕ → Ω → ℕ}

private lemma ae_tendsto_countMean (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (hint : Integrable (fun ω => (X 0 ω : ℝ)) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => countMean (fun i : Fin n => X i ω)) atTop
      (𝓝 μ[fun ω => (X 0 ω : ℝ)]) := by
  have hc : Measurable (fun k : ℕ => (k : ℝ)) := measurable_from_nat
  filter_upwards [strong_law_ae (fun i ω => (X i ω : ℝ)) hint
    (fun i j hij => (hindep hij).comp hc hc) (fun i => (hident i).comp hc)] with ω hω
  simpa [countMean, Fin.sum_univ_eq_sum_range (fun i => (X i ω : ℝ)), div_eq_inv_mul] using hω

private lemma ae_tendsto_digammaIncrement {a : ℝ} (ha : 0 < a) (hmeas : Measurable (X 0))
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (hint : Integrable (fun ω => (X 0 ω : ℝ)) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, digammaIncrement a (X i ω)) atTop
      (𝓝 μ[fun ω => digammaIncrement a (X 0 ω)]) := by
  have hc : Measurable (fun k : ℕ => digammaIncrement a k) := measurable_from_nat
  have hint' : Integrable (fun ω => digammaIncrement a (X 0 ω)) μ := by
    refine (hint.div_const a).mono' (hc.comp hmeas).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    have h := digammaIncrement_mem_Icc ha (X 0 ω)
    rw [Real.norm_of_nonneg h.1]; exact h.2
  filter_upwards [strong_law_ae (fun i ω => digammaIncrement a (X i ω)) hint'
    (fun i j hij => (hindep hij).comp hc hc) (fun i => (hident i).comp hc)] with ω hω
  simpa [Fin.sum_univ_eq_sum_range (fun i => digammaIncrement a (X i ω))] using hω

/-- **Strong consistency of the rate MLE at a known shape.** Let `X₀, X₁, …` be pairwise
independent, identically distributed counts with mean `E X₀ = σ a / b` (the marginal mean of the
hierarchy with size factor `σ > 0`, shape `a > 0` and rate `b > 0`). Almost surely, for all large
`n` the rate MLE `b̂ₙ = σ a / Mₙ` at the true shape solves the rate score equation of the first `n`
counts, and `b̂ₙ → b`. -/
theorem ae_tendsto_rateMLE {a b σ : ℝ} (ha : 0 < a) (hb : 0 < b) (hσ : 0 < σ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hint : Integrable (fun ω => (X 0 ω : ℝ)) μ) (hmean : μ[fun ω => (X 0 ω : ℝ)] = σ * a / b) :
    ∀ᵐ ω ∂μ, (∀ᶠ n in atTop, rateScore a (σ * a / countMean (fun i : Fin n => X i ω))
        (fun _ : Fin n => σ) (fun i => X i ω) = 0) ∧
      Tendsto (fun n => σ * a / countMean (fun i : Fin n => X i ω)) atTop (𝓝 b) := by
  filter_upwards [ae_tendsto_countMean hindep hident hint] with ω hω
  rw [hmean] at hω
  have hm : 0 < σ * a / b := by positivity
  refine ⟨?_, ?_⟩
  · filter_upwards [hω.eventually (lt_mem_nhds hm)] with n hn
    have : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · simp [countMean] at hn
      · exact h
    have : Nonempty (Fin n) := ⟨⟨0, this⟩⟩
    exact rateScore_const_eq_zero ha hσ hn
  · have h := (tendsto_const_nhds (x := σ * a)).div hω hm.ne'
    rwa [show σ * a / (σ * a / b) = b by field_simp] at h

/-- **Consistency of a root of the score equations (Cramér).** Let `X₀, X₁, …` be
pairwise independent, identically distributed counts, observed at a common size factor `σ > 0`,
with mean `E X₀ = σ a₀ / b₀`, the marginal mean of the hierarchy at the true hyperparameters
`a₀, b₀ > 0`. Assume local identifiability of the shape: the population profile shape score
`popProfileShapeScore μ X₀` is positive just left of `a₀` and negative just right of it. Then
almost surely, for every `ε > 0` and all large `n`, the score equations of the first `n` counts
have a solution `(â, b̂)` with `|â - a₀| < ε` and `|b̂ - b₀| < ε`: there is a strongly consistent
sequence of roots of the score equations.

For the negative binomial marginal law the sign hypothesis follows from the identity
`E[∑_{j<X₀} 1 / (a₀ + j)] = log (1 + σ / b₀)` (the expected shape score vanishes at the truth)
together with positivity of the profile information at `a₀`; neither is proved here, so the
crossing is assumed. The tests show the hypotheses can hold together, for a two-point count law
(values `0` and `3`, which is not negative binomial) with `a₀ ∈ (3/10, 1/2)` given by the
intermediate value theorem. The mean hypothesis is the proved marginal mean of `marginalLik`
(`marginalLik_eq_negBinomialReal`, `ProbabilityTheory.hasSum_mul_negBinomialReal`). -/
theorem ae_eventually_exists_score_root {a₀ b₀ σ : ℝ} (ha₀ : 0 < a₀) (hb₀ : 0 < b₀)
    (hσ : 0 < σ) (hmeas : Measurable (X 0)) (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (hint : Integrable (fun ω => (X 0 ω : ℝ)) μ)
    (hmean : μ[fun ω => (X 0 ω : ℝ)] = σ * a₀ / b₀)
    (hsign : ∀ᶠ ε in 𝓝[>] 0, 0 < popProfileShapeScore μ (X 0) (a₀ - ε) ∧
      popProfileShapeScore μ (X 0) (a₀ + ε) < 0) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ n in atTop, ∃ a b, 0 < a ∧ 0 < b ∧ |a - a₀| < ε ∧ |b - b₀| < ε ∧
      shapeScore a b (fun _ : Fin n => σ) (fun i => X i ω) = 0 ∧
      rateScore a b (fun _ : Fin n => σ) (fun i => X i ω) = 0 := by
  set m := σ * a₀ / b₀ with hm_def
  have hm : 0 < m := by positivity
  set η : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hη
  have hplus : ∀ᵐ ω ∂μ, ∀ j, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      ∑ i : Fin n, digammaIncrement (a₀ + η j) (X i ω)) atTop
      (𝓝 μ[fun ω => digammaIncrement (a₀ + η j) (X 0 ω)]) :=
    ae_all_iff.2 fun j => ae_tendsto_digammaIncrement (by positivity) hmeas hindep hident hint
  have hminus : ∀ᵐ ω ∂μ, ∀ j, η j < a₀ → Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      ∑ i : Fin n, digammaIncrement (a₀ - η j) (X i ω)) atTop
      (𝓝 μ[fun ω => digammaIncrement (a₀ - η j) (X 0 ω)]) := by
    refine ae_all_iff.2 fun j => ?_
    by_cases hj : η j < a₀
    · filter_upwards [ae_tendsto_digammaIncrement (sub_pos.2 hj) hmeas hindep hident hint]
        with ω hω _ using hω
    · exact ae_of_all _ fun ω h => absurd h hj
  filter_upwards [ae_tendsto_countMean hindep hident hint, hplus, hminus] with ω hM hωp hωm
  rw [hmean] at hM
  intro ε hε
  have hcont : ContinuousAt (fun p : ℝ × ℝ => p.1 * σ / p.2) (a₀, m) :=
    ((continuous_fst.mul continuous_const).continuousAt).div continuous_snd.continuousAt hm.ne'
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hcont ε hε
  have hb₀ : a₀ * σ / m = b₀ := by rw [hm_def]; field_simp
  obtain ⟨u, hu, hu'⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hsign
  have hu0 : (0 : ℝ) < u := hu
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (lt_min (lt_min hε hδ) (lt_min hu0 ha₀))
  have hj' : η j < min (min ε δ) (min u a₀) := hj
  have hηpos : 0 < η j := by positivity
  have hηε : η j < ε := lt_of_lt_of_le hj' ((min_le_left _ _).trans (min_le_left _ _))
  have hηδ : η j < δ := lt_of_lt_of_le hj' ((min_le_left _ _).trans (min_le_right _ _))
  have hηu : η j < u := lt_of_lt_of_le hj' ((min_le_right _ _).trans (min_le_left _ _))
  have hηa : η j < a₀ := lt_of_lt_of_le hj' ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hGm, hGp⟩ := hu' ⟨hηpos, hηu⟩
  have hlim : ∀ a, 0 < a → Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      ∑ i : Fin n, digammaIncrement a (X i ω)) atTop
        (𝓝 μ[fun ω => digammaIncrement a (X 0 ω)]) →
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, digammaIncrement a (X i ω) -
        (log (a + countMean (fun i : Fin n => X i ω)) - log a)) atTop
        (𝓝 (popProfileShapeScore μ (X 0) a)) := fun a ha h => by
    rw [popProfileShapeScore, hmean]
    exact h.sub (((hM.const_add a).log (by positivity)).sub tendsto_const_nhds)
  have em := (hlim _ (sub_pos.2 hηa) (hωm j hηa)).eventually (lt_mem_nhds hGm)
  have ep := (hlim _ (by positivity) (hωp j)).eventually (gt_mem_nhds hGp)
  have eM := hM.eventually (Metric.ball_mem_nhds m (lt_min hδ hm))
  filter_upwards [em, ep, eM] with n hm' hp' hMn
  rw [Real.dist_eq] at hMn
  have hMn' := abs_lt.1 hMn
  have hMpos : 0 < countMean (fun i : Fin n => X i ω) := by
    linarith [min_le_right δ m]
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp [countMean] at hMpos
    · exact h
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hrel : ∀ a, (n : ℝ)⁻¹ * profileShapeScore a (fun i : Fin n => X i ω) =
      (n : ℝ)⁻¹ * ∑ i : Fin n, digammaIncrement a (X i ω) -
        (log (a + countMean (fun i : Fin n => X i ω)) - log a) := fun a => by
    simpa using inv_card_mul_profileShapeScore (a := a) (fun i : Fin n => X i ω)
  have hninv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  have hPm : 0 < profileShapeScore (a₀ - η j) (fun i : Fin n => X i ω) := by
    rw [← hrel] at hm'; exact (mul_pos_iff_of_pos_left hninv).1 hm'
  have hPp : profileShapeScore (a₀ + η j) (fun i : Fin n => X i ω) < 0 := by
    rw [← hrel] at hp'
    by_contra hc
    nlinarith [mul_nonneg hninv.le (not_lt.1 hc)]
  obtain ⟨a, ha, hPa⟩ := intermediate_value_Icc' (by linarith : a₀ - η j ≤ a₀ + η j)
    ((continuousOn_profileShapeScore _ hMpos.le).mono fun x hx => (by linarith [hx.1] : 0 < x))
    ⟨hPp.le, hPm.le⟩
  have ha0 : 0 < a := by linarith [ha.1]
  have hb : 0 < σ * a / countMean (fun i : Fin n => X i ω) := by positivity
  have hroot := (score_eq_zero_iff_const ha0 hb hσ hMpos).2 ⟨rfl, hPa⟩
  have haη : |a - a₀| < δ ∧ |a - a₀| < ε := by
    have : |a - a₀| ≤ η j := abs_sub_le_iff.2 ⟨by linarith [ha.2], by linarith [ha.1]⟩
    exact ⟨by linarith, by linarith⟩
  refine ⟨a, _, ha0, hb, haη.2, ?_, hroot⟩
  have hd : dist (a, countMean (fun i : Fin n => X i ω)) (a₀, m) < δ := by
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    exact ⟨haη.1, lt_of_lt_of_le hMn (min_le_left _ _)⟩
  have h := hδε hd
  rw [Real.dist_eq, hb₀] at h
  rwa [show σ * a / countMean (fun i : Fin n => X i ω) =
    a * σ / countMean (fun i : Fin n => X i ω) by ring]

end Sampling

end MathlibExt.Biology.Omics.HierarchicalCount
