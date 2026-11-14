/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Omics.HierarchicalCountMLE

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import MathlibExt.Biology.Omics.HierarchicalCountMLEUniqueness

/-!
# Maximum marginal likelihood for the Gamma–Poisson hierarchy at heterogeneous size factors

`MathlibExt.Biology.Omics.HierarchicalCountMLE` (T86) defines the log marginal likelihood
`logMarginalLik a b s k = ∑ᵢ log NB(kᵢ; a, sᵢ a / b)` of counts `kᵢ` at size factors `sᵢ`, with one
rate `λᵢ ~ Gamma(a, b)` per cell, and its shape and rate scores `shapeScore`, `rateScore`. Its
conditional results (unique rate root at a fixed shape, unique shape root at a fixed rate) already
allow per-cell size factors, but its joint results (closed-form rate root `σ a / M`, existence of a
solution of the score equations under `M < V`, consistency) assume a common size factor `σ`. This
file treats the joint (shape, rate) estimation with a different size factor `sᵢ` for every cell.
The model is the intercept-only negative binomial regression with offsets `log sᵢ`
(Lawless 1987).

## Main definitions

* `rateRoot a s k`: the rate root `b̂(a)`, the unique positive root of the rate score equation at
  the shape `a` (no closed form when the `sᵢ` differ).
* `profileShapeScoreVarying a s k = shapeScore a (b̂(a)) s k`: the profile shape score.
* `pooledMean s k = (∑ᵢ kᵢ) / (∑ᵢ sᵢ)`: the pooled Poisson rate `μ̂`.
* `popRateScoreLog`, `popShapeScore`: the population rate score (in the log rate) and shape score of
  a cell with random size factor `S` and count `K`.

## Main results

* Score equations: `score_eq_zero_iff_rateRoot` (the joint score equations hold iff `b = b̂(a)`
  and `a` is a zero of the profile); `rateRoot_spec`, `rateRoot_eq` (characterization);
  `rateRoot_const`, `profileShapeScoreVarying_const` (at a common size factor they are T86's
  closed forms).
* The rate root: `rateRoot_strictMonoOn` (increasing in the shape), `continuousOn_rateRoot`,
  `div_le_sum_of_rateScore_eq_zero` (`a / b̂(a) ≤ ∑ᵢ kᵢ / sᵢ`), `tendsto_div_rateRoot` (the
  fitted prior mean `a / b̂(a)` tends to `μ̂` as `a → ∞`).
* Existence: `exists_score_root_of_overdispersed_varying`. If `∑ᵢ (kᵢ - sᵢ μ̂)² > ∑ᵢ kᵢ`, the
  joint score equations have a solution with `a, b > 0`. The condition says that the residual sum
  of squares around the fitted Poisson means exceeds their sum; it is the positivity of the
  numerator of the Dean–Lawless (1989) score statistic for overdispersion. At a common size factor
  it is T86's `M < V` (`overdispersed_const_iff`). The proof uses the profile: `b̂` is continuous,
  the profile is positive near `a = 0`, and by `sq_mul_shapeScore_le` and `tendsto_div_rateRoot`
  `a² · profile(a)` is at most a term tending to `(∑ᵢ kᵢ - ∑ᵢ (kᵢ - sᵢ μ̂)²) / 2 < 0` as `a → ∞`.
* Uniqueness at a common size factor, under the condition above:
  `existsUnique_score_root_const_varying` (exactly one positive root of the joint score
  equations), `profileShapeScoreVarying_eq_zero_unique_const`, and
  `existsUnique_isMaxOn_logMarginalLik_const_varying` (exactly one joint MLE). These restate the
  Levin–Reeds theorem of `HierarchicalCountMLEUniqueness` (T173) in this file's terms, through
  `overdispersed_const_iff` and `profileShapeScoreVarying_const`.
* Heterogeneous size factors, roots from sign changes: `exists_score_root_of_mem_uIcc` (a sign
  change of the profile on `[a₁, a₂]` gives a root there) and `exists_two_score_roots` (two sign
  changes give two roots with different shapes). The tests apply it to size factors
  `(1000, 1/100, 100)` and counts `(12, 1, 6)`, which satisfy `∑ᵢ (kᵢ - sᵢ μ̂)² > ∑ᵢ kᵢ`: there
  the joint score equations have two positive roots. So uniqueness of the root does not extend
  from a common size factor to heterogeneous ones.
* Consistency, with i.i.d. pairs `(Sᵢ, Kᵢ)` of a positive size factor and a count:
  `ae_tendsto_rateRoot` (strong consistency of `b̂ₙ(a)` for the population rate root);
  `popRateScoreLog_eq_zero_of_condMean` (the true `(a₀, b₀)` solve the population rate equation
  when `E[K ∣ S] = a₀ S / b₀`); `ae_eventually_exists_score_root_varying` (Cramér: a strongly
  consistent sequence of roots of the joint score equations, under local identifiability of the
  shape).

## Source receipt

* Model and score equations: Gamma–Poisson hierarchy, empirical-Bayes hyperparameter estimation
  (Robbins 1956, Morris 1983); negative binomial regression with offsets (Lawless 1987). Score
  equations are T86's `hasDerivAt_logMarginalLik_shape`, `hasDerivAt_logMarginalLik_rate`, which
  already allow per-cell size factors and are reused here.
* Existence: common size factor: Anscombe (1950), Aragón, Eberly and Eberly (1992). The
  heterogeneous condition is the Dean–Lawless (1989) overdispersion score numerator
  `∑ᵢ ((kᵢ - μ̂ᵢ)² - kᵢ)` at the Poisson fit `μ̂ᵢ = sᵢ μ̂`. No published existence theorem in
  exactly this form was found; the statement is proved here, not transcribed.
* Uniqueness at a common size factor: Levin and Reeds (1977), Theorem 2, proved in
  `HierarchicalCountMLEUniqueness`; also Aragón, Eberly and Eberly (1992).
* Non-uniqueness at heterogeneous size factors: not from the literature. The evidence is the two
  samples in the tests: `s = (1000, 1/100, 100)`, `k = (12, 1, 6)`, which satisfies the
  overdispersion condition, and `s = (100, 1)`, `k = (2, 1)`, which fails it. For both, the sign
  changes of the profile are proved from the definitions, with exact rational rate roots.
* Consistency: Cramér (1946), consistent root of the likelihood equations.

## Not proved here

* At heterogeneous size factors: uniqueness of the joint MLE (the tests show that the score root
  is not unique, not where the likelihood attains its maximum), that a root of the score
  equations maximizes the likelihood, and any converse for `∑ᵢ (kᵢ - sᵢ μ̂)² ≤ ∑ᵢ kᵢ`. The
  common-size-factor converse (no root, no MLE) fails here: the tests give a sample at size
  factors `(100, 1)` that violates the condition and still has two roots. A sufficient
  condition for uniqueness at heterogeneous size factors is not proved.
* The sign hypothesis of `ae_eventually_exists_score_root_varying` is assumed: deriving it for
  negative binomial counts needs the identity `E[∑_{j<K} 1 / (a₀ + j) ∣ S] = log (1 + S / b₀)`,
  which T86 also leaves unproved. The conditional-mean hypothesis of
  `popRateScoreLog_eq_zero_of_condMean` is stated, not derived from the count law, because the
  count law of a random variable is not formalized (as in `HierarchicalCount`).
* Asymptotic normality and efficiency.

## Implementation notes

Uniqueness at a common size factor is imported from `HierarchicalCountMLEUniqueness` (T173), not
reproved. Reuse (search of `MathlibExt`, `CSLibExt`, `WantedExt` and Mathlib on 2026-11-12 for
size factor, offset, negative binomial MLE, overdispersion, implicit root continuity): the
definitions and conditional results come from `HierarchicalCountMLE`, which is merged (#1623) and
imported, not edited. `MathlibExt.Probability.Statistics.GLM.NegativeBinomialDispersion` and
`GLM.CountData.Model` treat negative binomial regression with offsets in the (shape, mean)
parametrization with consistency hypotheses assumed abstractly, and prove no existence theorem.
The third-order bound on `digammaIncrement` is `HierarchicalCountMLE`'s public
`digammaIncrement_le_cubic`; `log (1 + x) ≥ x - x² / 2`, a private lemma there, is derived here
from Mathlib's `Real.le_log_one_add_of_nonneg`. The strong law is Mathlib's
`ProbabilityTheory.strong_law_ae`. Continuity of `b̂` is a short implicit-root argument (private)
from strict monotonicity of `b ↦ b · ∂ℓ/∂b`; no Mathlib lemma packages it.

## References

* F. J. Anscombe, *Sampling theory of the negative binomial and logarithmic series
  distributions*, Biometrika 37 (1950), 358–382.
* J. Aragón, D. Eberly and S. Eberly, *Existence and uniqueness of the maximum likelihood
  estimator for the two-parameter negative binomial distribution*, Statist. Probab. Lett. 15
  (1992), 375–379.
* H. Cramér, *Mathematical Methods of Statistics*, Princeton University Press, 1946.
* C. Dean and J. F. Lawless, *Tests for detecting overdispersion in Poisson regression models*,
  J. Amer. Statist. Assoc. 84 (1989), 467–472.
* B. Levin and J. Reeds, *Compound multinomial likelihood functions are unimodal: proof of a
  conjecture of I. J. Good*, Ann. Statist. 5 (1977), 79–87.
* J. F. Lawless, *Negative binomial and mixed Poisson regression*, Canad. J. Statist. 15 (1987),
  209–225.
* C. N. Morris, *Parametric empirical Bayes inference: theory and applications*, J. Amer.
  Statist. Assoc. 78 (1983), 47–55.
* H. Robbins, *An empirical Bayes approach to statistics*, Proc. Third Berkeley Symp. Math.
  Statist. Prob. 1 (1956), 157–163.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology Finset Function

namespace MathlibExt.Biology.Omics.HierarchicalCount

variable {ι : Type*} [Fintype ι]

/-! ### The rate root at a fixed shape -/

open Classical in
/-- The rate root `b̂(a)`: the positive solution of the rate score equation
`∑ᵢ (a / b - (a + kᵢ) / (b + sᵢ)) = 0` at the shape `a`, and `0` if there is none. For `a > 0`,
positive size factors and some positive count it exists and is unique
(`exists_rateScore_eq_zero`, `rateScore_eq_zero_unique`), see `rateRoot_spec`; with a common size
factor `σ` it is the closed form `σ a / M` (`rateRoot_const`). -/
noncomputable def rateRoot (a : ℝ) (s : ι → ℝ) (k : ι → ℕ) : ℝ :=
  if h : ∃ b, 0 < b ∧ rateScore a b s k = 0 then h.choose else 0

/-- The profile shape score `a ↦ ∂ℓ/∂a (a, b̂(a))`, the shape score along the rate root. Its
positive zeros are exactly the shapes of the positive solutions of the joint score equations
(`score_eq_zero_iff_rateRoot`). With a common size factor `σ` it is `profileShapeScore`
(`profileShapeScoreVarying_const`). -/
noncomputable def profileShapeScoreVarying (a : ℝ) (s : ι → ℝ) (k : ι → ℕ) : ℝ :=
  shapeScore a (rateRoot a s k) s k

/-- The pooled Poisson rate `μ̂ = (∑ᵢ kᵢ) / (∑ᵢ sᵢ)`: the prior mean `a / b` fitted by the rate
score equation in the Poisson limit `a → ∞` (`tendsto_div_rateRoot`). -/
noncomputable def pooledMean (s : ι → ℝ) (k : ι → ℕ) : ℝ := (∑ i, (k i : ℝ)) / ∑ i, s i

private lemma rateScoreLog_eq_zero {a b : ℝ} (hb : 0 < b) {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    {k : ι → ℕ} (h : rateScore a b s k = 0) : rateScoreLog a b s k = 0 := by
  rw [← rateScore_mul_self hb hs, h, zero_mul]

private lemma rateScore_eq_zero_of_log {a b : ℝ} (hb : 0 < b) {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    {k : ι → ℕ} (h : rateScoreLog a b s k = 0) : rateScore a b s k = 0 := by
  have := rateScore_mul_self (a := a) hb hs k
  rw [h] at this
  exact (mul_eq_zero.1 this).resolve_right hb.ne'

/-- **The rate root solves the rate score equation.** For `a > 0`, positive size factors and some
positive count, `b̂(a) > 0` and `∂ℓ/∂b (a, b̂(a)) = 0`. -/
theorem rateRoot_spec {a : ℝ} [Nonempty ι] (ha : 0 < a) {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    {k : ι → ℕ} (hk : ∃ i, 0 < k i) :
    0 < rateRoot a s k ∧ rateScore a (rateRoot a s k) s k = 0 := by
  have h := exists_rateScore_eq_zero ha hs hk
  rw [rateRoot, dite_eq_left h]
  exact h.choose_spec

/-- **Characterization of the rate root.** Any positive root of the rate score equation at the
shape `a > 0` is `b̂(a)`. -/
theorem rateRoot_eq {a b : ℝ} [Nonempty ι] (ha : 0 < a) (hb : 0 < b) {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) {k : ι → ℕ} (h : rateScore a b s k = 0) : rateRoot a s k = b := by
  have hex : ∃ b, 0 < b ∧ rateScore a b s k = 0 := ⟨b, hb, h⟩
  have hspec := hex.choose_spec
  rw [rateRoot, dite_eq_left hex]
  exact rateScore_eq_zero_unique ha hspec.1 hb hs hspec.2 h

/-- **Common size factor.** At a common size factor `σ > 0` the rate root is `σ a / M`. -/
theorem rateRoot_const {a σ : ℝ} [Nonempty ι] (ha : 0 < a) (hσ : 0 < σ) {k : ι → ℕ}
    (hM : 0 < countMean k) : rateRoot a (fun _ => σ) k = σ * a / countMean k :=
  rateRoot_eq ha (by positivity) (fun _ => hσ) (rateScore_const_eq_zero ha hσ hM)

/-- At a common size factor `σ > 0` the profile shape score along the rate root is T86's
`profileShapeScore`. -/
theorem profileShapeScoreVarying_const {a σ : ℝ} [Nonempty ι] (ha : 0 < a) (hσ : 0 < σ)
    {k : ι → ℕ} (hM : 0 < countMean k) :
    profileShapeScoreVarying a (fun _ => σ) k = profileShapeScore a k := by
  rw [profileShapeScoreVarying, rateRoot_const ha hσ hM, shapeScore_const_rateRoot ha hσ hM]

/-- **The joint score equations reduce to the profile.** For `a, b > 0`, `(a, b)` solves both
score equations iff `b = b̂(a)` and `a` is a zero of the profile shape score. -/
theorem score_eq_zero_iff_rateRoot {a b : ℝ} [Nonempty ι] (ha : 0 < a) (hb : 0 < b)
    {s : ι → ℝ} (hs : ∀ i, 0 < s i) {k : ι → ℕ} :
    shapeScore a b s k = 0 ∧ rateScore a b s k = 0 ↔
      b = rateRoot a s k ∧ profileShapeScoreVarying a s k = 0 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    have e := (rateRoot_eq ha hb hs h₂).symm
    exact ⟨e, by rw [profileShapeScoreVarying, ← e, h₁]⟩
  · rintro ⟨rfl, h⟩
    refine ⟨h, ?_⟩
    have hk : ∃ i, 0 < k i := by
      by_contra hc
      push Not at hc
      have hb' : 0 < rateRoot a s k := hb
      have hex : ∃ b, 0 < b ∧ rateScore a b s k = 0 := by
        by_contra hne
        rw [rateRoot, dite_eq_right hne] at hb'
        exact lt_irrefl _ hb'
      obtain ⟨c, hc0, hcr⟩ := hex
      linarith [rateScore_pos_of_counts_eq_zero ha hc0 hs fun i => Nat.le_zero.1 (hc i)]
    exact (rateRoot_spec ha hs hk).2

/-- **The rate root increases with the shape.** For `0 < a < a'`, `b̂(a) < b̂(a')`. -/
theorem rateRoot_strictMonoOn [Nonempty ι] {s : ι → ℝ} (hs : ∀ i, 0 < s i) {k : ι → ℕ}
    (hk : ∃ i, 0 < k i) : StrictMonoOn (fun a => rateRoot a s k) (Set.Ioi 0) := by
  intro a ha a' ha' hlt
  change rateRoot a s k < rateRoot a' s k
  have ha : (0 : ℝ) < a := ha
  have ha' : (0 : ℝ) < a' := ha'
  obtain ⟨hb, hr⟩ := rateRoot_spec ha hs hk
  obtain ⟨hb', hr'⟩ := rateRoot_spec ha' hs hk
  have h0 := rateScoreLog_eq_zero hb hs hr
  have h0' := rateScoreLog_eq_zero hb' hs hr'
  set b := rateRoot a s k
  set b' := rateRoot a' s k
  have hinc : rateScoreLog a b s k < rateScoreLog a' b s k := by
    refine sum_lt_sum_of_nonempty univ_nonempty fun i _ => ?_
    have hsi := hs i
    have : b / (b + s i) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    nlinarith
  by_contra hc
  rcases (not_lt.1 hc).lt_or_eq with h | h
  · linarith [rateScoreLog_strictAnti ha' hb' h hs k]
  · rw [h] at h0'; linarith

/-- **A lower bound on the rate root.** At a positive root `b` of the rate score equation the
fitted prior mean `a / b` is at most `∑ᵢ kᵢ / sᵢ`: otherwise every term `a / b - (a + kᵢ) /
(b + sᵢ) = (a sᵢ - b kᵢ) / (b (b + sᵢ))` would be positive. -/
theorem div_le_sum_of_rateScore_eq_zero {a b : ℝ} [Nonempty ι] (hb : 0 < b) {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) {k : ι → ℕ} (h : rateScore a b s k = 0) :
    a / b ≤ ∑ i, (k i : ℝ) / s i := by
  by_contra hc
  push Not at hc
  have hpos : 0 < rateScore a b s k := by
    refine sum_pos (fun i _ => ?_) univ_nonempty
    have hsi := hs i
    have hle : (k i : ℝ) / s i ≤ ∑ j, (k j : ℝ) / s j :=
      single_le_sum (f := fun j => (k j : ℝ) / s j) (fun j _ => by have := hs j; positivity)
        (mem_univ i)
    have hlt : (k i : ℝ) / s i < a / b := lt_of_le_of_lt hle hc
    rw [div_lt_div_iff₀ hsi hb] at hlt
    rw [sub_pos, div_lt_div_iff₀ (by linarith) hb]
    nlinarith
  linarith

private lemma continuousAt_of_strictAnti_root {F : ℝ → ℝ → ℝ} {r : ℝ → ℝ} {a₀ : ℝ}
    (hF : ∀ b, 0 < b → ContinuousAt (fun a => F a b) a₀)
    (hanti : ∀ᶠ a in 𝓝 a₀, StrictAntiOn (F a) (Set.Ioi 0))
    (hr : ∀ᶠ a in 𝓝 a₀, 0 < r a ∧ F a (r a) = 0) : ContinuousAt r a₀ := by
  have h₀ := hr.self_of_nhds
  have hanti₀ := hanti.self_of_nhds
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · set c := max l (r a₀ / 2)
    have hc0 : 0 < c := lt_max_of_lt_right (by linarith [h₀.1])
    have hcr : c < r a₀ := max_lt hl (by linarith [h₀.1])
    have hpos : 0 < F a₀ c := by
      have := hanti₀ (Set.mem_Ioi.2 hc0) (Set.mem_Ioi.2 h₀.1) hcr; linarith [h₀.2]
    filter_upwards [(hF c hc0).eventually (lt_mem_nhds hpos), hanti, hr] with a hFa ha hra
    by_contra hle
    have hle : r a ≤ c := (not_lt.1 hle).trans (le_max_left _ _)
    rcases hle.lt_or_eq with hlt | heq
    · have := ha (Set.mem_Ioi.2 hra.1) (Set.mem_Ioi.2 hc0) hlt; linarith [hra.2]
    · have := hra.2; rw [heq] at this; linarith
  · have hu0 : 0 < u := lt_trans h₀.1 hu
    have hneg : F a₀ u < 0 := by
      have := hanti₀ (Set.mem_Ioi.2 h₀.1) (Set.mem_Ioi.2 hu0) hu; linarith [h₀.2]
    filter_upwards [(hF u hu0).eventually (gt_mem_nhds hneg), hanti, hr] with a hFa ha hra
    by_contra hle
    rcases (not_lt.1 hle).lt_or_eq with hlt | heq
    · have := ha (Set.mem_Ioi.2 hu0) (Set.mem_Ioi.2 hra.1) hlt; linarith [hra.2]
    · have := hra.2; rw [← heq] at this; linarith

/-- **Continuity of the rate root.** With positive size factors and some positive count,
`a ↦ b̂(a)` is continuous on `a > 0` (implicit-function argument from the strict monotonicity of
`b ↦ b ∂ℓ/∂b`). -/
theorem continuousOn_rateRoot [Nonempty ι] {s : ι → ℝ} (hs : ∀ i, 0 < s i) {k : ι → ℕ}
    (hk : ∃ i, 0 < k i) : ContinuousOn (fun a => rateRoot a s k) (Set.Ioi 0) := by
  intro a₀ ha₀
  refine ContinuousAt.continuousWithinAt
    (continuousAt_of_strictAnti_root (F := fun a b => rateScoreLog a b s k) ?_ ?_ ?_)
  · intro b _
    simp only [rateScoreLog]
    fun_prop
  · filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < a₀ from ha₀)] with a ha
    intro x hx y _ hxy
    exact rateScoreLog_strictAnti (show (0 : ℝ) < a from ha) hx hxy hs k
  · filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < a₀ from ha₀)] with a ha
    obtain ⟨hb, hr⟩ := rateRoot_spec (show (0 : ℝ) < a from ha) hs hk
    exact ⟨hb, rateScoreLog_eq_zero hb hs hr⟩

private lemma continuousAt_digammaIncrement {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ContinuousAt (fun x => digammaIncrement x k) a :=
  tendsto_finsetSum _ fun j _ => (continuousAt_id.add continuousAt_const).inv₀ (by
    have : 0 < a + (j : ℝ) := by positivity
    exact this.ne')

/-- **Continuity of the profile shape score** on `a > 0` (positive size factors, some positive
count). -/
theorem continuousOn_profileShapeScoreVarying [Nonempty ι] {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    {k : ι → ℕ} (hk : ∃ i, 0 < k i) :
    ContinuousOn (fun a => profileShapeScoreVarying a s k) (Set.Ioi 0) := by
  intro a ha
  have ha : (0 : ℝ) < a := ha
  have hr : ContinuousAt (fun a => rateRoot a s k) a :=
    (continuousOn_rateRoot hs hk).continuousAt (Ioi_mem_nhds ha)
  have hb := (rateRoot_spec ha hs hk).1
  refine ContinuousAt.continuousWithinAt ?_
  exact tendsto_finsetSum _ fun i _ => ((continuousAt_digammaIncrement ha (k i)).add
    (hr.log hb.ne')).sub ((hr.add continuousAt_const).log (add_pos hb (hs i)).ne')

/-! ### Existence of a solution of the joint score equations -/

private lemma shapeScore_eq_sub {a b : ℝ} (hb : 0 < b) {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    (k : ι → ℕ) :
    shapeScore a b s k = ∑ i, (digammaIncrement a (k i) - log (1 + s i / b)) := by
  refine sum_congr rfl fun i _ => ?_
  have hsi := hs i
  have : log (b + s i) = log b + log (1 + s i / b) := by
    rw [← log_mul hb.ne' (by positivity)]
    congr 1
    field_simp
  rw [this]
  ring

/-- `log (1 + x) ≥ x - x² / 2` for `x ≥ 0`, from Mathlib's `log (1 + x) ≥ 2 x / (x + 2)`. -/
private lemma sub_sq_div_two_le_log_one_add {x : ℝ} (hx : 0 ≤ x) : x - x ^ 2 / 2 ≤ log (1 + x) := by
  refine le_trans ?_ (le_log_one_add_of_nonneg hx)
  rw [le_div_iff₀ (by linarith)]
  nlinarith [pow_nonneg hx 3]

private lemma shapeScore_term_le {a m : ℝ} (ha : 0 < a) (hm : 0 ≤ m) (k : ℕ) :
    a ^ 2 * (digammaIncrement a k - log (1 + m / a)) ≤
      ((k : ℝ) - ((k : ℝ) - m) ^ 2) / 2 + (m - k) * m ^ 2 / (a + m) + (k : ℝ) ^ 3 / a -
        a * (a * (m - k) / (a + m)) := by
  have hd := digammaIncrement_le_cubic ha k
  have hl := sub_sq_div_two_le_log_one_add (x := m / a) (by positivity)
  have ham : a + m ≠ 0 := by linarith
  calc a ^ 2 * (digammaIncrement a k - log (1 + m / a)) ≤
        a ^ 2 * ((k / a - (k * (k - 1) / 2) / a ^ 2 + (k : ℝ) ^ 3 / a ^ 3) -
          (m / a - (m / a) ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg a)
    _ = _ := by field_simp; ring

private lemma rateScoreLog_eq_sum_fitted {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) (k : ι → ℕ) :
    rateScoreLog a b s k = ∑ i, a * (s i * (a / b) - k i) / (a + s i * (a / b)) := by
  refine sum_congr rfl fun i _ => ?_
  have hsi := hs i
  have h1 : b + s i ≠ 0 := by linarith
  have h2 : a + s i * (a / b) ≠ 0 := by positivity
  field_simp
  ring

/-- **The second-order bound behind overdispersion.** At a positive root `b` of the rate score
equation, with fitted means `mᵢ = sᵢ a / b`,
`a² ∂ℓ/∂a ≤ ∑ᵢ ((kᵢ - (kᵢ - mᵢ)²) / 2 + (mᵢ - kᵢ) mᵢ² / (a + mᵢ) + kᵢ³ / a)`. The leading term
`(∑ᵢ kᵢ - ∑ᵢ (kᵢ - mᵢ)²) / 2` is negative for overdispersed samples. -/
theorem sq_mul_shapeScore_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) {k : ι → ℕ} (h : rateScore a b s k = 0) :
    a ^ 2 * shapeScore a b s k ≤ ∑ i, (((k i : ℝ) - ((k i : ℝ) - s i * (a / b)) ^ 2) / 2 +
      (s i * (a / b) - k i) * (s i * (a / b)) ^ 2 / (a + s i * (a / b)) + (k i : ℝ) ^ 3 / a) := by
  have hL := rateScoreLog_eq_zero hb hs h
  rw [rateScoreLog_eq_sum_fitted ha hb hs] at hL
  have hm : ∀ i, s i / b = s i * (a / b) / a := fun i => by field_simp
  rw [shapeScore_eq_sub hb hs, mul_sum]
  calc ∑ i, a ^ 2 * (digammaIncrement a (k i) - log (1 + s i / b)) ≤
        ∑ i, ((((k i : ℝ) - ((k i : ℝ) - s i * (a / b)) ^ 2) / 2 +
          (s i * (a / b) - k i) * (s i * (a / b)) ^ 2 / (a + s i * (a / b)) +
            (k i : ℝ) ^ 3 / a) - a * (a * (s i * (a / b) - k i) / (a + s i * (a / b)))) :=
        sum_le_sum fun i _ => by
          rw [hm i]; exact shapeScore_term_le ha (by have := hs i; positivity) (k i)
    _ = _ := by rw [sum_sub_distrib, ← mul_sum, hL, mul_zero, sub_zero]

private lemma sum_counts_pos_of_overdispersed {s : ι → ℝ} {k : ι → ℕ}
    (hQ : ∑ i, (k i : ℝ) < ∑ i, ((k i : ℝ) - s i * pooledMean s k) ^ 2) : ∃ i, 0 < k i := by
  by_contra hc
  push Not at hc
  have hk : ∀ i, (k i : ℝ) = 0 := fun i => by simp [Nat.le_zero.1 (hc i)]
  simp [pooledMean, hk] at hQ

private lemma sum_div_pos [Nonempty ι] {s : ι → ℝ} (hs : ∀ i, 0 < s i) {k : ι → ℕ}
    (hk : ∃ i, 0 < k i) : 0 < ∑ i, (k i : ℝ) / s i := by
  obtain ⟨i₀, hi₀⟩ := hk
  exact sum_pos' (fun i _ => by have := hs i; positivity)
    ⟨i₀, mem_univ _, div_pos (by exact_mod_cast hi₀) (hs i₀)⟩

/-- **The fitted prior mean tends to the pooled Poisson rate.** With positive size factors and
some positive count, `a / b̂(a) → μ̂ = (∑ᵢ kᵢ) / (∑ᵢ sᵢ)` as `a → ∞` (the Poisson limit). -/
theorem tendsto_div_rateRoot [Nonempty ι] {s : ι → ℝ} (hs : ∀ i, 0 < s i) {k : ι → ℕ}
    (hk : ∃ i, 0 < k i) :
    Tendsto (fun a => a / rateRoot a s k) atTop (𝓝 (pooledMean s k)) := by
  set U := ∑ i, (k i : ℝ) / s i
  have hS : 0 < ∑ i, s i := sum_pos (fun i _ => hs i) univ_nonempty
  set R : ℝ → ℝ := fun a => ∑ i, (s i * (a / rateRoot a s k) - k i) *
    (s i * (a / rateRoot a s k)) / (a + s i * (a / rateRoot a s k))
  have hid : ∀ a, 0 < a → a / rateRoot a s k = ((∑ i, (k i : ℝ)) + R a) / ∑ i, s i := by
    intro a ha
    obtain ⟨hb, hr⟩ := rateRoot_spec ha hs hk
    have hL := rateScoreLog_eq_zero hb hs hr
    rw [rateScoreLog_eq_sum_fitted ha hb hs] at hL
    set μ := a / rateRoot a s k
    have hμ : 0 < μ := div_pos ha hb
    rw [eq_div_iff hS.ne']
    have hRa : R a = ∑ i, (s i * μ - k i) * (s i * μ) / (a + s i * μ) := rfl
    rw [hRa]
    clear_value μ
    have : μ * ∑ i, s i - ∑ i, (k i : ℝ) =
        ∑ i, (s i * μ - k i) * (s i * μ) / (a + s i * μ) := by
      have e : μ * ∑ i, s i - ∑ i, (k i : ℝ) = ∑ i, (s i * μ - k i) := by
        rw [sum_sub_distrib, mul_sum]; simp_rw [mul_comm μ]
      rw [e]
      have e2 : ∑ i, (s i * μ - k i) = ∑ i, a * (s i * μ - k i) / (a + s i * μ) +
          ∑ i, (s i * μ - k i) * (s i * μ) / (a + s i * μ) := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun i _ => ?_
        have : a + s i * μ ≠ 0 := by have := hs i; positivity
        field_simp
      rw [e2, hL, zero_add]
    linarith
  have hR : Tendsto R atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds
      (x := ∑ i, (s i * U + k i) * (s i * U))).div_atTop tendsto_id)
    filter_upwards [eventually_gt_atTop 0] with a ha
    obtain ⟨hb, hr⟩ := rateRoot_spec ha hs hk
    have hμ : 0 < a / rateRoot a s k := div_pos ha hb
    have hμU : a / rateRoot a s k ≤ U := div_le_sum_of_rateScore_eq_zero hb hs hr
    set μ := a / rateRoot a s k
    rw [Real.norm_eq_abs, id, sum_div]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
    have hsi := hs i
    have hk0 : (0 : ℝ) ≤ k i := (k i).cast_nonneg
    have hsμ : 0 ≤ s i * μ := by positivity
    have hsμU : s i * μ ≤ s i * U := mul_le_mul_of_nonneg_left hμU hsi.le
    rw [abs_div, abs_mul, abs_of_nonneg hsμ, abs_of_pos (by linarith : 0 < a + s i * μ)]
    refine div_le_div₀ (mul_nonneg (by linarith) (by linarith)) ?_ ha (by linarith)
    exact mul_le_mul (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩) hsμU hsμ (by linarith)
  have hlim : Tendsto (fun a => ((∑ i, (k i : ℝ)) + R a) / ∑ i, s i) atTop
      (𝓝 (((∑ i, (k i : ℝ)) + 0) / ∑ i, s i)) :=
    (tendsto_const_nhds.add hR).div_const _
  rw [add_zero] at hlim
  exact hlim.congr' (by
    filter_upwards [eventually_gt_atTop 0] with a ha using (hid a ha).symm)

private lemma eventually_profileShapeScoreVarying_neg [Nonempty ι] {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) {k : ι → ℕ}
    (hQ : ∑ i, (k i : ℝ) < ∑ i, ((k i : ℝ) - s i * pooledMean s k) ^ 2) :
    ∀ᶠ a in atTop, profileShapeScoreVarying a s k < 0 := by
  have hk := sum_counts_pos_of_overdispersed hQ
  have hμ := tendsto_div_rateRoot hs hk
  set E : ℝ → ℝ := fun a => ∑ i, (((k i : ℝ) - ((k i : ℝ) - s i * (a / rateRoot a s k)) ^ 2) / 2 +
      (s i * (a / rateRoot a s k) - k i) * (s i * (a / rateRoot a s k)) ^ 2 /
        (a + s i * (a / rateRoot a s k)) + (k i : ℝ) ^ 3 / a)
  have hE : Tendsto E atTop
      (𝓝 (∑ i, (((k i : ℝ) - ((k i : ℝ) - s i * pooledMean s k) ^ 2) / 2 + 0 + 0))) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    have hm : Tendsto (fun a => s i * (a / rateRoot a s k)) atTop (𝓝 (s i * pooledMean s k)) :=
      tendsto_const_nhds.mul hμ
    refine (((tendsto_const_nhds.sub ((tendsto_const_nhds.sub hm).pow 2)).div_const 2).add
      ?_).add (tendsto_const_nhds.div_atTop tendsto_id)
    exact ((hm.sub tendsto_const_nhds).mul (hm.pow 2)).div_atTop (tendsto_id.atTop_add hm)
  have hneg : ∑ i, (((k i : ℝ) - ((k i : ℝ) - s i * pooledMean s k) ^ 2) / 2 + 0 + 0) < 0 := by
    simp only [add_zero, ← sum_div, sum_sub_distrib]
    linarith
  filter_upwards [hE.eventually (gt_mem_nhds hneg), eventually_gt_atTop 0] with a hEa ha
  obtain ⟨hb, hr⟩ := rateRoot_spec ha hs hk
  have hle := sq_mul_shapeScore_le ha hb hs hr
  rw [profileShapeScoreVarying]
  by_contra hc
  have : 0 ≤ a ^ 2 * shapeScore a (rateRoot a s k) s k := mul_nonneg (sq_nonneg a) (not_lt.1 hc)
  have hEa' : E a < 0 := hEa
  linarith

private lemma exists_profileShapeScoreVarying_pos [Nonempty ι] {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    {k : ι → ℕ} (hk : ∃ i, 0 < k i) : ∃ a, 0 < a ∧ 0 < profileShapeScoreVarying a s k := by
  set U := ∑ i, (k i : ℝ) / s i
  have hU : 0 < U := sum_div_pos hs hk
  obtain ⟨i₀, hi₀⟩ := hk
  set g : ℝ → ℝ := fun x => 1 - ∑ i, (x * log (x + s i * U) - x * log x) with hg
  have hgc : ContinuousAt g 0 := continuousAt_const.sub (tendsto_finsetSum _ fun i _ =>
    (continuousAt_id.mul ((continuousAt_id.add continuousAt_const).log
      (by simpa using (mul_pos (hs i) hU).ne'))).sub
        Real.continuous_mul_log.continuousAt)
  have hg0 : (0 : ℝ) < g 0 := by simp [hg]
  obtain ⟨a, hga, ha⟩ := (((hgc.eventually (lt_mem_nhds hg0)).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  have ha : (0 : ℝ) < a := ha
  refine ⟨a, ha, ?_⟩
  obtain ⟨hb, hr⟩ := rateRoot_spec ha hs ⟨i₀, hi₀⟩
  have hμU : a / rateRoot a s k ≤ U := div_le_sum_of_rateScore_eq_zero hb hs hr
  set b := rateRoot a s k
  have hsum : a⁻¹ ≤ ∑ i, digammaIncrement a (k i) := by
    refine le_trans ?_ (single_le_sum (fun i _ => (digammaIncrement_mem_Icc ha _).1)
      (mem_univ i₀))
    rw [digammaIncrement]
    simpa using single_le_sum (f := fun j : ℕ => (a + j)⁻¹) (fun j _ => by positivity)
      (mem_range.2 hi₀)
  have hlog : ∀ i, a * log (1 + s i / b) ≤ a * log (a + s i * U) - a * log a := fun i => by
    have hsi := hs i
    have e : log (a + s i * U) - log a = log (1 + s i * U / a) := by
      rw [← log_div (by positivity) ha.ne']; congr 1; field_simp
    rw [← mul_sub, e]
    refine mul_le_mul_of_nonneg_left (log_le_log (by positivity) ?_) ha.le
    have : s i / b = s i * (a / b) / a := by field_simp
    rw [this]
    gcongr
  have hprod : g a ≤ a * profileShapeScoreVarying a s k := by
    have h1 : 1 ≤ a * ∑ i, digammaIncrement a (k i) := by
      have := mul_le_mul_of_nonneg_left hsum ha.le
      rwa [mul_inv_cancel₀ ha.ne'] at this
    rw [profileShapeScoreVarying, shapeScore_eq_sub hb hs, sum_sub_distrib, mul_sub]
    simp only [hg]
    have := sum_le_sum fun i (_ : i ∈ univ) => hlog i
    rw [← mul_sum] at this
    linarith
  by_contra hc
  have := mul_nonpos_of_nonneg_of_nonpos ha.le (not_lt.1 hc)
  linarith

/-- **Overdispersion gives a solution of the score equations, heterogeneous size factors.** Let
`μ̂ = (∑ᵢ kᵢ) / (∑ᵢ sᵢ)` be the pooled Poisson rate and `sᵢ μ̂` the fitted Poisson means. If the
Pearson-type excess `∑ᵢ (kᵢ - sᵢ μ̂)² > ∑ᵢ kᵢ` holds (residual sum of squares above the summed
Poisson variances; at a common size factor this is `M < V`, see `overdispersed_const_iff`), then
the joint score equations have a solution `(â, b̂)` with `â, b̂ > 0`. At a common size factor it
is unique (`existsUnique_score_root_const_varying`); at heterogeneous size factors it need not be
(`exists_two_score_roots` and the tests). That a solution maximizes the likelihood is not proved
here. -/
theorem exists_score_root_of_overdispersed_varying [Nonempty ι] {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) {k : ι → ℕ}
    (hQ : ∑ i, (k i : ℝ) < ∑ i, ((k i : ℝ) - s i * pooledMean s k) ^ 2) :
    ∃ a b, 0 < a ∧ 0 < b ∧ shapeScore a b s k = 0 ∧ rateScore a b s k = 0 := by
  have hk := sum_counts_pos_of_overdispersed hQ
  obtain ⟨a₁, ha₁, hP₁⟩ := exists_profileShapeScoreVarying_pos hs hk
  obtain ⟨a₂, hP₂, ha₂⟩ :=
    ((eventually_profileShapeScoreVarying_neg hs hQ).and (eventually_gt_atTop a₁)).exists
  obtain ⟨a, ha, hPa⟩ := intermediate_value_Icc' ha₂.le
    ((continuousOn_profileShapeScoreVarying hs hk).mono fun x hx =>
      (lt_of_lt_of_le ha₁ hx.1 : 0 < x)) ⟨hP₂.le, hP₁.le⟩
  have ha0 : 0 < a := lt_of_lt_of_le ha₁ ha.1
  have hb := (rateRoot_spec ha0 hs hk).1
  exact ⟨a, _, ha0, hb, (score_eq_zero_iff_rateRoot ha0 hb hs).2 ⟨rfl, hPa⟩⟩

/-- **The overdispersion condition at a common size factor.** For `s ≡ σ > 0` the condition of
`exists_score_root_of_overdispersed_varying`, `∑ᵢ (kᵢ - σ μ̂)² > ∑ᵢ kᵢ`, is T86's `M < V`. -/
theorem overdispersed_const_iff {σ : ℝ} [Nonempty ι] (hσ : 0 < σ) (k : ι → ℕ) :
    ∑ i, (k i : ℝ) < ∑ i, ((k i : ℝ) - (fun _ => σ) i * pooledMean (fun _ => σ) k) ^ 2 ↔
      countMean k < countVar k := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hM : σ * pooledMean (fun _ : ι => σ) k = countMean k := by
    simp only [pooledMean, countMean, sum_const, card_univ, nsmul_eq_mul]
    field_simp
  have hA : ∑ i, (k i : ℝ) = Fintype.card ι * countMean k := by rw [countMean]; field_simp
  have hB : ∑ i, ((k i : ℝ) - countMean k) ^ 2 = Fintype.card ι * countVar k := by
    have e : ∑ i, ((k i : ℝ) - countMean k) ^ 2 =
        ∑ i, (k i : ℝ) ^ 2 - 2 * countMean k * ∑ i, (k i : ℝ) +
          Fintype.card ι * countMean k ^ 2 := by
      simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
        mul_sum]
      congr 1; congr 1; exact sum_congr rfl fun i _ => by ring
    rw [e, hA, countVar]; field_simp; ring
  simp only [hM, hB, hA]
  exact mul_lt_mul_iff_right₀ hn

/-! ### Uniqueness at a common size factor -/

private lemma countMean_pos_of_overdispersed [Nonempty ι] {σ : ℝ} {k : ι → ℕ}
    (hQ : ∑ i, (k i : ℝ) < ∑ i, ((k i : ℝ) - σ * pooledMean (fun _ => σ) k) ^ 2) :
    0 < countMean k := by
  obtain ⟨i₀, hi₀⟩ := sum_counts_pos_of_overdispersed (s := fun _ => σ) hQ
  rw [countMean]
  refine div_pos (sum_pos' (fun i _ => (k i).cast_nonneg) ⟨i₀, mem_univ _, ?_⟩) ?_
  · exact_mod_cast hi₀
  · exact_mod_cast Fintype.card_pos

/-- **Uniqueness of the joint score root at a common size factor** (Levin and Reeds 1977,
Theorem 2, proved in `HierarchicalCountMLEUniqueness` as `existsUnique_score_root`). At `s ≡ σ > 0`
and under the overdispersion condition of `exists_score_root_of_overdispersed_varying`, the joint
score equations have exactly one positive solution. -/
theorem existsUnique_score_root_const_varying [Nonempty ι] {σ : ℝ} (hσ : 0 < σ) {k : ι → ℕ}
    (hQ : ∑ i, (k i : ℝ) < ∑ i, ((k i : ℝ) - σ * pooledMean (fun _ => σ) k) ^ 2) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ shapeScore p.1 p.2 (fun _ => σ) k = 0 ∧
      rateScore p.1 p.2 (fun _ => σ) k = 0 :=
  existsUnique_score_root hσ (countMean_pos_of_overdispersed hQ)
    ((overdispersed_const_iff hσ k).1 hQ)

/-- **The profile shape score has at most one positive zero at a common size factor**, under the
overdispersion condition (Levin and Reeds 1977, via `profileShapeScore_eq_zero_unique`). -/
theorem profileShapeScoreVarying_eq_zero_unique_const [Nonempty ι] {σ : ℝ} (hσ : 0 < σ)
    {k : ι → ℕ} (hQ : ∑ i, (k i : ℝ) < ∑ i, ((k i : ℝ) - σ * pooledMean (fun _ => σ) k) ^ 2)
    {a a' : ℝ} (ha : 0 < a) (ha' : 0 < a') (h : profileShapeScoreVarying a (fun _ => σ) k = 0)
    (h' : profileShapeScoreVarying a' (fun _ => σ) k = 0) : a = a' := by
  have hM := countMean_pos_of_overdispersed hQ
  rw [profileShapeScoreVarying_const ha hσ hM] at h
  rw [profileShapeScoreVarying_const ha' hσ hM] at h'
  exact profileShapeScore_eq_zero_unique ((overdispersed_const_iff hσ k).1 hQ) ha ha' h h'

/-- **Existence and uniqueness of the joint MLE at a common size factor** (Levin and Reeds 1977,
via `existsUnique_isMaxOn_logMarginalLik`), under the overdispersion condition of
`exists_score_root_of_overdispersed_varying`: `ℓ` has exactly one maximizer over `(0, ∞)²`. -/
theorem existsUnique_isMaxOn_logMarginalLik_const_varying [Nonempty ι] {σ : ℝ} (hσ : 0 < σ)
    {k : ι → ℕ} (hQ : ∑ i, (k i : ℝ) < ∑ i, ((k i : ℝ) - σ * pooledMean (fun _ => σ) k) ^ 2) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ ∀ q : ℝ × ℝ, 0 < q.1 → 0 < q.2 →
      logMarginalLik q.1 q.2 (fun _ => σ) k ≤ logMarginalLik p.1 p.2 (fun _ => σ) k :=
  existsUnique_isMaxOn_logMarginalLik hσ (countMean_pos_of_overdispersed hQ)
    ((overdispersed_const_iff hσ k).1 hQ)

/-! ### Heterogeneous size factors: score roots from sign changes of the profile -/

/-- **A root of the joint score equations from a sign change of the profile.** If `0` lies
between the profile shape scores at `0 < a₁ ≤ a₂`, then some `a ∈ [a₁, a₂]` with its rate root
`b̂(a) > 0` solves both score equations. -/
theorem exists_score_root_of_mem_uIcc [Nonempty ι] {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    {k : ι → ℕ} (hk : ∃ i, 0 < k i) {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (h12 : a₁ ≤ a₂)
    (h0 : (0 : ℝ) ∈ Set.uIcc (profileShapeScoreVarying a₁ s k) (profileShapeScoreVarying a₂ s k)) :
    ∃ a ∈ Set.Icc a₁ a₂, 0 < rateRoot a s k ∧ shapeScore a (rateRoot a s k) s k = 0 ∧
      rateScore a (rateRoot a s k) s k = 0 := by
  have hcont : ContinuousOn (fun a => profileShapeScoreVarying a s k) (Set.uIcc a₁ a₂) := by
    rw [Set.uIcc_of_le h12]
    exact (continuousOn_profileShapeScoreVarying hs hk).mono fun x hx =>
      (lt_of_lt_of_le ha₁ hx.1 : 0 < x)
  obtain ⟨a, ha, hPa⟩ := intermediate_value_uIcc hcont h0
  rw [Set.uIcc_of_le h12] at ha
  obtain ⟨hb, hr⟩ := rateRoot_spec (lt_of_lt_of_le ha₁ ha.1) hs hk
  exact ⟨a, ha, hb, hPa, hr⟩

/-- **Two sign changes of the profile give two roots.** If `0` lies between the profile shape
scores at `a₁` and `a₂` and between those at `a₂` and `a₃`, with `0 < a₁ < a₂ < a₃`, and the
profile does not vanish at `a₂`, the joint score equations have two positive solutions with
different shapes. The tests exhibit such samples at heterogeneous size factors, one of them
satisfying the overdispersion condition of `exists_score_root_of_overdispersed_varying`; so
`existsUnique_score_root_const_varying` does not extend to heterogeneous size factors. -/
theorem exists_two_score_roots [Nonempty ι] {s : ι → ℝ} (hs : ∀ i, 0 < s i) {k : ι → ℕ}
    (hk : ∃ i, 0 < k i) {a₁ a₂ a₃ : ℝ} (ha₁ : 0 < a₁) (h12 : a₁ < a₂) (h23 : a₂ < a₃)
    (h₁₂ : (0 : ℝ) ∈
      Set.uIcc (profileShapeScoreVarying a₁ s k) (profileShapeScoreVarying a₂ s k))
    (h₂₃ : (0 : ℝ) ∈
      Set.uIcc (profileShapeScoreVarying a₂ s k) (profileShapeScoreVarying a₃ s k))
    (h₂ : profileShapeScoreVarying a₂ s k ≠ 0) :
    ∃ a b a' b', 0 < a ∧ 0 < b ∧ 0 < a' ∧ 0 < b' ∧ a < a' ∧
      shapeScore a b s k = 0 ∧ rateScore a b s k = 0 ∧
      shapeScore a' b' s k = 0 ∧ rateScore a' b' s k = 0 := by
  obtain ⟨a, ha, hb, hs₁, hr₁⟩ := exists_score_root_of_mem_uIcc hs hk ha₁ h12.le h₁₂
  obtain ⟨a', ha', hb', hs₂, hr₂⟩ :=
    exists_score_root_of_mem_uIcc hs hk (ha₁.trans h12) h23.le h₂₃
  have hne : a ≠ a₂ := by
    rintro rfl
    exact h₂ hs₁
  exact ⟨a, _, a', _, lt_of_lt_of_le ha₁ ha.1, hb, lt_of_lt_of_le (ha₁.trans h12) ha'.1, hb',
    lt_of_lt_of_le (lt_of_le_of_ne ha.2 hne) ha'.1, hs₁, hr₁, hs₂, hr₂⟩

/-! ### Consistency with random size factors -/

section Sampling

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {S : ℕ → Ω → ℝ} {X : ℕ → Ω → ℕ}

/-- The population rate score in the log rate, for a cell with random size factor `S` and count
`K`: `a - E[(a + K) · b / (b + S)]`, the almost sure limit of `n⁻¹ · rateScoreLog a b` for i.i.d.
copies of `(S, K)` (`ae_tendsto_rateRoot`). -/
noncomputable def popRateScoreLog (μ : Measure Ω) (S : Ω → ℝ) (K : Ω → ℕ) (a b : ℝ) : ℝ :=
  a - μ[fun ω => (a + K ω) * (b / (b + S ω))]

/-- The population shape score `E[∑_{j<K} 1 / (a + j) - log (1 + S / b)]`, the almost sure limit of
`n⁻¹ · shapeScore a b` for i.i.d. copies of `(S, K)`. -/
noncomputable def popShapeScore (μ : Measure Ω) (S : Ω → ℝ) (K : Ω → ℕ) (a b : ℝ) : ℝ :=
  μ[fun ω => digammaIncrement a (K ω) - log (1 + S ω / b)]

private lemma measurable_rateTerm (a b : ℝ) :
    Measurable fun x : ℝ × ℕ => (a + (x.2 : ℝ)) * (b / (b + x.1)) :=
  (measurable_const.add (measurable_from_nat.comp measurable_snd)).mul
    (measurable_const.div (measurable_const.add measurable_fst))

private lemma measurable_shapeTerm (a b : ℝ) :
    Measurable fun x : ℝ × ℕ => digammaIncrement a x.2 - log (1 + x.1 / b) := by
  have h1 : Measurable fun x : ℝ × ℕ => digammaIncrement a x.2 :=
    (measurable_from_nat (f := fun k => digammaIncrement a k)).comp measurable_snd
  have h2 : Measurable fun x : ℝ × ℕ => log (1 + x.1 / b) :=
    (measurable_const.add (measurable_fst.div_const b)).log
  exact h1.sub h2

private lemma integrable_rateTerm {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) {S₀ : Ω → ℝ} {K : Ω → ℕ}
    (hS : Measurable S₀) (hK : Measurable K) (hpos : ∀ ω, 0 < S₀ ω)
    (hint : Integrable (fun ω => (K ω : ℝ)) μ) :
    Integrable (fun ω => (a + K ω) * (b / (b + S₀ ω))) μ := by
  refine ((integrable_const a).add hint).mono'
    ((measurable_rateTerm a b).comp (hS.prodMk hK)).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  have h1 : 0 ≤ b / (b + S₀ ω) := div_nonneg hb.le (by linarith [hpos ω])
  have h2 : b / (b + S₀ ω) ≤ 1 := (div_le_one (by linarith [hpos ω])).2 (by linarith [hpos ω])
  have hK0 : (0 : ℝ) ≤ K ω := (K ω).cast_nonneg
  simp only [Pi.add_apply]
  rw [Real.norm_of_nonneg (by positivity)]
  nlinarith

omit [IsProbabilityMeasure μ] in
private lemma integrable_shapeTerm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {S₀ : Ω → ℝ}
    {K : Ω → ℕ} (hS : Measurable S₀) (hK : Measurable K) (hpos : ∀ ω, 0 < S₀ ω)
    (hint : Integrable (fun ω => (K ω : ℝ)) μ) (hintS : Integrable S₀ μ) :
    Integrable (fun ω => digammaIncrement a (K ω) - log (1 + S₀ ω / b)) μ := by
  refine ((hint.div_const a).add (hintS.div_const b)).mono'
    ((measurable_shapeTerm a b).comp (hS.prodMk hK)).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  have hd := digammaIncrement_mem_Icc ha (K ω)
  have hx : 0 ≤ S₀ ω / b := div_nonneg (hpos ω).le hb.le
  have hl0 : 0 ≤ log (1 + S₀ ω / b) := log_nonneg (by linarith)
  have hl1 : log (1 + S₀ ω / b) ≤ S₀ ω / b := by
    have := log_le_sub_one_of_pos (show 0 < 1 + S₀ ω / b by linarith); linarith
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_le]; constructor <;> linarith [hd.1, hd.2]

omit [IsProbabilityMeasure μ] in
private lemma ae_tendsto_avg {f : ℝ × ℕ → ℝ} (hf : Measurable f)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω => (S i ω, X i ω)))
    (hident : ∀ i, IdentDistrib (fun ω => (S i ω, X i ω)) (fun ω => (S 0 ω, X 0 ω)) μ μ)
    (hint : Integrable (fun ω => f (S 0 ω, X 0 ω)) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, f (S i ω, X i ω)) atTop
      (𝓝 μ[fun ω => f (S 0 ω, X 0 ω)]) := by
  filter_upwards [strong_law_ae (fun i ω => f (S i ω, X i ω)) hint
    (fun i j hij => (hindep hij).comp hf hf) (fun i => (hident i).comp hf)] with ω hω
  simpa [Fin.sum_univ_eq_sum_range (fun i => f (S i ω, X i ω))] using hω

private lemma inv_mul_rateScoreLog {a b : ℝ} {n : ℕ} (hn : 0 < n) (s : Fin n → ℝ)
    (k : Fin n → ℕ) :
    (n : ℝ)⁻¹ * rateScoreLog a b s k = a - (n : ℝ)⁻¹ * ∑ i, (a + k i) * (b / (b + s i)) := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [rateScoreLog, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_sub, ← mul_assoc, inv_mul_cancel₀ this, one_mul]

private lemma ae_tendsto_rateScoreLog {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hmeas : ∀ i, Measurable (S i) ∧ Measurable (X i)) (hpos : ∀ i ω, 0 < S i ω)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω => (S i ω, X i ω)))
    (hident : ∀ i, IdentDistrib (fun ω => (S i ω, X i ω)) (fun ω => (S 0 ω, X 0 ω)) μ μ)
    (hint : Integrable (fun ω => (X 0 ω : ℝ)) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      rateScoreLog a b (fun i : Fin n => S i ω) (fun i => X i ω)) atTop
      (𝓝 (popRateScoreLog μ (S 0) (X 0) a b)) := by
  filter_upwards [ae_tendsto_avg (measurable_rateTerm a b) hindep hident
    (integrable_rateTerm ha hb (hmeas 0).1 (hmeas 0).2 (hpos 0) hint)] with ω hω
  refine (tendsto_const_nhds.sub hω).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (inv_mul_rateScoreLog hn _ _).symm

omit [IsProbabilityMeasure μ] in
private lemma ae_tendsto_shapeScore {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hmeas : ∀ i, Measurable (S i) ∧ Measurable (X i)) (hpos : ∀ i ω, 0 < S i ω)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω => (S i ω, X i ω)))
    (hident : ∀ i, IdentDistrib (fun ω => (S i ω, X i ω)) (fun ω => (S 0 ω, X 0 ω)) μ μ)
    (hint : Integrable (fun ω => (X 0 ω : ℝ)) μ) (hintS : Integrable (S 0) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      shapeScore a b (fun i : Fin n => S i ω) (fun i => X i ω)) atTop
      (𝓝 (popShapeScore μ (S 0) (X 0) a b)) := by
  filter_upwards [ae_tendsto_avg (measurable_shapeTerm a b) hindep hident
    (integrable_shapeTerm ha hb (hmeas 0).1 (hmeas 0).2 (hpos 0) hint hintS)] with ω hω
  refine hω.congr' (Eventually.of_forall fun n => ?_)
  simp only
  rw [shapeScore_eq_sub (s := fun i : Fin n => S i ω) hb fun i => hpos i ω]

/-- **The population rate score decreases in the rate.** -/
theorem popRateScoreLog_strictAnti {a b b' : ℝ} (ha : 0 < a) (hb : 0 < b) (hbb' : b < b')
    {S₀ : Ω → ℝ} {K : Ω → ℕ} (hS : Measurable S₀) (hK : Measurable K) (hpos : ∀ ω, 0 < S₀ ω)
    (hint : Integrable (fun ω => (K ω : ℝ)) μ) :
    popRateScoreLog μ S₀ K a b' < popRateScoreLog μ S₀ K a b := by
  have hb' : 0 < b' := hb.trans hbb'
  have i1 := integrable_rateTerm (μ := μ) ha.le hb hS hK hpos hint
  have i2 := integrable_rateTerm (μ := μ) ha.le hb' hS hK hpos hint
  have hlt : ∀ ω, (a + K ω) * (b / (b + S₀ ω)) < (a + K ω) * (b' / (b' + S₀ ω)) := fun ω => by
    have := hpos ω
    have hK0 : (0 : ℝ) ≤ K ω := (K ω).cast_nonneg
    refine mul_lt_mul_of_pos_left ?_ (by positivity)
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have hpos' : 0 < μ[fun ω => (a + K ω) * (b' / (b' + S₀ ω)) - (a + K ω) * (b / (b + S₀ ω))] := by
    rw [integral_pos_iff_support_of_nonneg (fun ω => (sub_pos.2 (hlt ω)).le) (i2.sub i1)]
    have : Function.support (fun ω => (a + K ω) * (b' / (b' + S₀ ω)) -
        (a + K ω) * (b / (b + S₀ ω))) = Set.univ :=
      Set.eq_univ_of_forall fun ω => (sub_pos.2 (hlt ω)).ne'
    rw [this, measure_univ]; exact one_pos
  rw [integral_sub i2 i1] at hpos'
  simp only [popRateScoreLog]
  linarith

/-- **The truth solves the population rate equation.** If the count has conditional mean
`E[K ∣ S] = a₀ S / b₀` (the hierarchy `K ∣ S, λ ~ Po(S λ)`, `λ ~ Gamma(a₀, b₀)` independent of
`S`), expressed as `E[K g(S)] = (a₀ / b₀) E[S g(S)]` for every bounded measurable `g`, then
`popRateScoreLog μ S K a₀ b₀ = 0`. -/
theorem popRateScoreLog_eq_zero_of_condMean {a₀ b₀ : ℝ} (hb₀ : 0 < b₀) {S₀ : Ω → ℝ}
    {K : Ω → ℕ} (hS : Measurable S₀) (hK : Measurable K) (hpos : ∀ ω, 0 < S₀ ω)
    (hint : Integrable (fun ω => (K ω : ℝ)) μ)
    (hcond : ∀ g : ℝ → ℝ, Measurable g → (∀ x, |g x| ≤ 1) →
      μ[fun ω => (K ω : ℝ) * g (S₀ ω)] = a₀ / b₀ * μ[fun ω => S₀ ω * g (S₀ ω)]) :
    popRateScoreLog μ S₀ K a₀ b₀ = 0 := by
  set g : ℝ → ℝ := fun x => b₀ / (b₀ + |x|) with hg
  have hgm : Measurable g := measurable_const.div (measurable_const.add continuous_abs.measurable)
  have hg1 : ∀ x, |g x| ≤ 1 := fun x => by
    have := abs_nonneg x
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).2 (by linarith)
  have hgS : ∀ ω, g (S₀ ω) = b₀ / (b₀ + S₀ ω) := fun ω => by
    change b₀ / (b₀ + |S₀ ω|) = _; rw [abs_of_pos (hpos ω)]
  have hc := hcond g hgm hg1
  simp only [hgS] at hc
  have hmS : Measurable fun ω => b₀ / (b₀ + S₀ ω) := measurable_const.div (measurable_const.add hS)
  have iG : Integrable (fun ω => b₀ / (b₀ + S₀ ω)) μ := by
    refine (integrable_const (1 : ℝ)).mono' hmS.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have := hpos ω
    rw [Real.norm_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).2 (by linarith)
  have iSG : Integrable (fun ω => S₀ ω * (b₀ / (b₀ + S₀ ω))) μ := by
    refine (integrable_const b₀).mono' (hS.mul hmS).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    have := hpos ω
    rw [Real.norm_of_nonneg (by positivity), mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have iKG : Integrable (fun ω => (K ω : ℝ) * (b₀ / (b₀ + S₀ ω))) μ := by
    refine hint.mono' ((measurable_from_nat.comp hK).mul hmS).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    have := hpos ω
    have hK0 : (0 : ℝ) ≤ K ω := (K ω).cast_nonneg
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right hK0 ((div_le_one (by positivity)).2 (by linarith))
  have hsplit : μ[fun ω => (a₀ + K ω) * (b₀ / (b₀ + S₀ ω))] =
      a₀ * μ[fun ω => b₀ / (b₀ + S₀ ω)] + μ[fun ω => (K ω : ℝ) * (b₀ / (b₀ + S₀ ω))] := by
    rw [← integral_const_mul, ← integral_add (iG.const_mul a₀) iKG]
    exact integral_congr_ae (ae_of_all _ fun ω => by simp only; ring)
  have hone : μ[fun ω => b₀ / (b₀ + S₀ ω)] + μ[fun ω => S₀ ω * (b₀ / (b₀ + S₀ ω))] / b₀ = 1 := by
    rw [← integral_div, ← integral_add iG (iSG.div_const b₀)]
    have : (fun ω => b₀ / (b₀ + S₀ ω) + S₀ ω * (b₀ / (b₀ + S₀ ω)) / b₀) = fun _ => (1 : ℝ) := by
      funext ω
      have := hpos ω
      field_simp
    rw [this, integral_const, probReal_univ, one_smul]
  rw [popRateScoreLog, hsplit, hc]
  have : a₀ * μ[fun ω => b₀ / (b₀ + S₀ ω)] + a₀ / b₀ * μ[fun ω => S₀ ω * (b₀ / (b₀ + S₀ ω))] =
      a₀ * (μ[fun ω => b₀ / (b₀ + S₀ ω)] + μ[fun ω => S₀ ω * (b₀ / (b₀ + S₀ ω))] / b₀) := by
    ring
  rw [this, hone, mul_one, sub_self]

private lemma rateRoot_lt_of_rateScoreLog_neg {a c : ℝ} [Nonempty ι] (ha : 0 < a) (hc : 0 < c)
    {s : ι → ℝ} (hs : ∀ i, 0 < s i) {k : ι → ℕ} (h : rateScoreLog a c s k < 0) :
    (∃ i, 0 < k i) ∧ rateRoot a s k < c := by
  have hk : ∃ i, 0 < k i := by
    by_contra hk
    push Not at hk
    have : 0 < rateScoreLog a c s k := by
      rw [← rateScore_mul_self hc hs]
      exact mul_pos (rateScore_pos_of_counts_eq_zero ha hc hs fun i => Nat.le_zero.1 (hk i)) hc
    linarith
  refine ⟨hk, ?_⟩
  obtain ⟨hb, hr⟩ := rateRoot_spec ha hs hk
  have h0 := rateScoreLog_eq_zero hb hs hr
  by_contra hle
  rcases (not_lt.1 hle).lt_or_eq with hlt | heq
  · linarith [rateScoreLog_strictAnti ha hc hlt hs k]
  · rw [← heq] at h0; linarith

private lemma lt_rateRoot_of_rateScoreLog_pos {a c : ℝ} [Nonempty ι] (ha : 0 < a)
    {s : ι → ℝ} (hs : ∀ i, 0 < s i) {k : ι → ℕ} (hk : ∃ i, 0 < k i)
    (h : 0 < rateScoreLog a c s k) : c < rateRoot a s k := by
  obtain ⟨hb, hr⟩ := rateRoot_spec ha hs hk
  have h0 := rateScoreLog_eq_zero hb hs hr
  by_contra hle
  rcases (not_lt.1 hle).lt_or_eq with hlt | heq
  · linarith [rateScoreLog_strictAnti ha hb hlt hs k]
  · rw [heq] at h0; linarith

private lemma nonempty_fin_of_inv_mul_ne {n : ℕ} {x : ℝ} (h : (n : ℝ)⁻¹ * x ≠ 0) :
    Nonempty (Fin n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at h
  · exact ⟨⟨0, hn⟩⟩

/-- **Strong consistency of the rate root, heterogeneous size factors.** Let `(S₀, X₀), (S₁, X₁), …`
be pairwise independent, identically distributed pairs of a positive size factor and a count, with
`X₀` integrable, and let `b₀ > 0` solve the population rate equation at the shape `a > 0`,
`popRateScoreLog μ S₀ X₀ a b₀ = 0` (at the true hyperparameters this follows from the conditional
mean, `popRateScoreLog_eq_zero_of_condMean`). Almost surely, for all large `n` the rate root
`b̂ₙ(a)` of the first `n` cells solves their rate score equation, and `b̂ₙ(a) → b₀`. -/
theorem ae_tendsto_rateRoot {a b₀ : ℝ} (ha : 0 < a) (hb₀ : 0 < b₀)
    (hmeas : ∀ i, Measurable (S i) ∧ Measurable (X i)) (hpos : ∀ i ω, 0 < S i ω)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω => (S i ω, X i ω)))
    (hident : ∀ i, IdentDistrib (fun ω => (S i ω, X i ω)) (fun ω => (S 0 ω, X 0 ω)) μ μ)
    (hint : Integrable (fun ω => (X 0 ω : ℝ)) μ)
    (hroot : popRateScoreLog μ (S 0) (X 0) a b₀ = 0) :
    ∀ᵐ ω ∂μ, (∀ᶠ n in atTop, rateScore a (rateRoot a (fun i : Fin n => S i ω) fun i => X i ω)
        (fun i : Fin n => S i ω) (fun i => X i ω) = 0) ∧
      Tendsto (fun n => rateRoot a (fun i : Fin n => S i ω) fun i => X i ω) atTop (𝓝 b₀) := by
  have hall : ∀ᵐ ω ∂μ, ∀ q : ℚ, 0 < (q : ℝ) → Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      rateScoreLog a q (fun i : Fin n => S i ω) (fun i => X i ω)) atTop
      (𝓝 (popRateScoreLog μ (S 0) (X 0) a q)) := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [ae_tendsto_rateScoreLog ha.le hq hmeas hpos hindep hident hint]
        with ω hω _ using hω
    · exact ae_of_all _ fun ω h => absurd h hq
  have hanti := fun {b b'} (hb : 0 < b) (hbb' : b < b') =>
    popRateScoreLog_strictAnti (μ := μ) ha hb hbb' (hmeas 0).1 (hmeas 0).2 (hpos 0) hint
  filter_upwards [hall] with ω hω
  -- above the root: eventually the sample rate score is negative, so the root lies below
  have hup : ∀ u, b₀ < u → ∀ᶠ n in atTop, ∃ _ : Nonempty (Fin n),
      (∃ i : Fin n, 0 < X i ω) ∧ rateRoot a (fun i : Fin n => S i ω) (fun i => X i ω) < u := by
    intro u hu
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hu
    have hq0 : 0 < (q : ℝ) := hb₀.trans hq1
    have hneg : popRateScoreLog μ (S 0) (X 0) a q < 0 := hroot ▸ hanti hb₀ hq1
    filter_upwards [(hω q hq0).eventually (gt_mem_nhds hneg)] with n hn
    have hne : Nonempty (Fin n) := nonempty_fin_of_inv_mul_ne hn.ne
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Fin.pos_iff_nonempty.2 hne
    have hL : rateScoreLog a q (fun i : Fin n => S i ω) (fun i => X i ω) < 0 := by
      by_contra hc
      have := mul_nonneg (inv_nonneg.2 hn0.le) (not_lt.1 hc)
      linarith
    obtain ⟨hk, hr⟩ := rateRoot_lt_of_rateScoreLog_neg ha hq0 (fun i : Fin n => hpos i ω) hL
    exact ⟨hne, hk, hr.trans hq2⟩
  refine ⟨?_, tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩⟩
  · filter_upwards [hup (b₀ + 1) (by linarith)] with n ⟨hne, hk, _⟩
    exact (rateRoot_spec ha (fun i : Fin n => hpos i ω) hk).2
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hl hb₀ : max l 0 < b₀)
    have hq0 : 0 < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq1
    have hposq : 0 < popRateScoreLog μ (S 0) (X 0) a q := hroot ▸ hanti hq0 hq2
    filter_upwards [(hω q hq0).eventually (lt_mem_nhds hposq), hup (b₀ + 1) (by linarith)]
      with n hn ⟨hne, hk, _⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Fin.pos_iff_nonempty.2 hne
    have hL : 0 < rateScoreLog a q (fun i : Fin n => S i ω) (fun i => X i ω) :=
      (mul_pos_iff_of_pos_left (inv_pos.2 hn0)).1 hn
    exact lt_of_le_of_lt (le_max_left _ _)
      (hq1.trans (lt_rateRoot_of_rateScoreLog_pos ha (fun i : Fin n => hpos i ω) hk hL))
  · filter_upwards [hup u hu] with n ⟨_, _, hr⟩ using hr

private lemma shapeScore_le_of_le {a b b' : ℝ} (hb : 0 < b) (hbb' : b ≤ b') {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) (k : ι → ℕ) : shapeScore a b s k ≤ shapeScore a b' s k := by
  rw [shapeScore_eq_sub hb hs, shapeScore_eq_sub (hb.trans_le hbb') hs]
  refine sum_le_sum fun i _ => ?_
  have hsi := hs i
  have : s i / b' ≤ s i / b := div_le_div_of_nonneg_left hsi.le hb hbb'
  have : log (1 + s i / b') ≤ log (1 + s i / b) :=
    log_le_log (by have := div_pos hsi (hb.trans_le hbb'); linarith) (by linarith)
  linarith

private lemma abs_popRateScoreLog_sub_le {a a' b : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') (hb : 0 < b)
    {S₀ : Ω → ℝ} {K : Ω → ℕ} (hS : Measurable S₀) (hK : Measurable K) (hpos : ∀ ω, 0 < S₀ ω)
    (hint : Integrable (fun ω => (K ω : ℝ)) μ) :
    |popRateScoreLog μ S₀ K a b - popRateScoreLog μ S₀ K a' b| ≤ |a - a'| := by
  have hmS : Measurable fun ω => b / (b + S₀ ω) := measurable_const.div (measurable_const.add hS)
  have iG : Integrable (fun ω => b / (b + S₀ ω)) μ := by
    refine (integrable_const (1 : ℝ)).mono' hmS.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have := hpos ω
    rw [Real.norm_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).2 (by linarith)
  have hG0 : 0 ≤ μ[fun ω => b / (b + S₀ ω)] :=
    integral_nonneg fun ω => by have := hpos ω; positivity
  have hG1 : μ[fun ω => b / (b + S₀ ω)] ≤ 1 := by
    have h := integral_mono iG (integrable_const (1 : ℝ)) fun ω => by
      have := hpos ω
      exact (div_le_one (by linarith : 0 < b + S₀ ω)).2 (by linarith)
    simpa using h
  have e : popRateScoreLog μ S₀ K a b - popRateScoreLog μ S₀ K a' b =
      (a - a') * (1 - μ[fun ω => b / (b + S₀ ω)]) := by
    simp only [popRateScoreLog]
    rw [show (a - μ[fun ω => (a + K ω) * (b / (b + S₀ ω))]) -
        (a' - μ[fun ω => (a' + K ω) * (b / (b + S₀ ω))]) = (a - a') -
        (μ[fun ω => (a + K ω) * (b / (b + S₀ ω))] -
          μ[fun ω => (a' + K ω) * (b / (b + S₀ ω))]) by ring,
      ← integral_sub (integrable_rateTerm ha hb hS hK hpos hint)
        (integrable_rateTerm ha' hb hS hK hpos hint)]
    have : (fun ω => (a + K ω) * (b / (b + S₀ ω)) - (a' + K ω) * (b / (b + S₀ ω))) =
        fun ω => (a - a') * (b / (b + S₀ ω)) := funext fun ω => by ring
    rw [this, integral_const_mul]
    ring
  rw [e, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (by rw [abs_of_nonneg (by linarith)]; linarith)

private lemma ae_all_rate {κ : Type*} [Countable κ] (A B : κ → ℝ)
    (hmeas : ∀ i, Measurable (S i) ∧ Measurable (X i)) (hpos : ∀ i ω, 0 < S i ω)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω => (S i ω, X i ω)))
    (hident : ∀ i, IdentDistrib (fun ω => (S i ω, X i ω)) (fun ω => (S 0 ω, X 0 ω)) μ μ)
    (hint : Integrable (fun ω => (X 0 ω : ℝ)) μ) :
    ∀ᵐ ω ∂μ, ∀ j, 0 < A j → 0 < B j → Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      rateScoreLog (A j) (B j) (fun i : Fin n => S i ω) (fun i => X i ω)) atTop
      (𝓝 (popRateScoreLog μ (S 0) (X 0) (A j) (B j))) := by
  refine ae_all_iff.2 fun j => ?_
  by_cases h : 0 < A j ∧ 0 < B j
  · filter_upwards [ae_tendsto_rateScoreLog h.1.le h.2 hmeas hpos hindep hident hint]
      with ω hω _ _ using hω
  · exact ae_of_all _ fun ω h1 h2 => absurd ⟨h1, h2⟩ h

omit [IsProbabilityMeasure μ] in
private lemma ae_all_shape {κ : Type*} [Countable κ] (A B : κ → ℝ)
    (hmeas : ∀ i, Measurable (S i) ∧ Measurable (X i)) (hpos : ∀ i ω, 0 < S i ω)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω => (S i ω, X i ω)))
    (hident : ∀ i, IdentDistrib (fun ω => (S i ω, X i ω)) (fun ω => (S 0 ω, X 0 ω)) μ μ)
    (hint : Integrable (fun ω => (X 0 ω : ℝ)) μ) (hintS : Integrable (S 0) μ) :
    ∀ᵐ ω ∂μ, ∀ j, 0 < A j → 0 < B j → Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      shapeScore (A j) (B j) (fun i : Fin n => S i ω) (fun i => X i ω)) atTop
      (𝓝 (popShapeScore μ (S 0) (X 0) (A j) (B j))) := by
  refine ae_all_iff.2 fun j => ?_
  by_cases h : 0 < A j ∧ 0 < B j
  · filter_upwards [ae_tendsto_shapeScore h.1 h.2 hmeas hpos hindep hident hint hintS]
      with ω hω _ _ using hω
  · exact ae_of_all _ fun ω h1 h2 => absurd ⟨h1, h2⟩ h

/-- **Consistency of a root of the joint score equations (Cramér), heterogeneous size factors.**
Let `(S₀, X₀), (S₁, X₁), …` be pairwise independent, identically distributed pairs of a positive
size factor and a count, both integrable, and let the true hyperparameters `a₀, b₀ > 0` solve the
population rate equation, `popRateScoreLog μ S₀ X₀ a₀ b₀ = 0` (which follows from the conditional
mean, `popRateScoreLog_eq_zero_of_condMean`). Assume local identifiability of the shape: for all
small `η > 0` there are rates at which the population rate and shape scores are both positive at
the shape `a₀ - η`, and rates at which both are negative at `a₀ + η` (a sign change of the
population profile shape score at `a₀`, stated without the population rate root). Then almost
surely, for every `ε > 0` and all large `n`, the score equations of the first `n` cells have a
solution `(â, b̂)` with `|â - a₀| < ε` and `|b̂ - b₀| < ε`.

The sign hypothesis is assumed, not derived from the negative binomial law: it rests on the
expected shape score vanishing at the truth, which is not proved here or in
`HierarchicalCountMLE`. -/
theorem ae_eventually_exists_score_root_varying {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hb₀ : 0 < b₀)
    (hmeas : ∀ i, Measurable (S i) ∧ Measurable (X i)) (hpos : ∀ i ω, 0 < S i ω)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω => (S i ω, X i ω)))
    (hident : ∀ i, IdentDistrib (fun ω => (S i ω, X i ω)) (fun ω => (S 0 ω, X 0 ω)) μ μ)
    (hint : Integrable (fun ω => (X 0 ω : ℝ)) μ) (hintS : Integrable (S 0) μ)
    (hroot : popRateScoreLog μ (S 0) (X 0) a₀ b₀ = 0)
    (hsign : ∀ᶠ η in 𝓝[>] 0,
      (∃ c, 0 < c ∧ 0 < popRateScoreLog μ (S 0) (X 0) (a₀ - η) c ∧
        0 < popShapeScore μ (S 0) (X 0) (a₀ - η) c) ∧
      (∃ c, 0 < c ∧ popRateScoreLog μ (S 0) (X 0) (a₀ + η) c < 0 ∧
        popShapeScore μ (S 0) (X 0) (a₀ + η) c < 0)) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ n in atTop, ∃ a b, 0 < a ∧ 0 < b ∧ |a - a₀| < ε ∧ |b - b₀| < ε ∧
      shapeScore a b (fun i : Fin n => S i ω) (fun i => X i ω) = 0 ∧
      rateScore a b (fun i : Fin n => S i ω) (fun i => X i ω) = 0 := by
  set R := popRateScoreLog μ (S 0) (X 0) with hR
  set G := popShapeScore μ (S 0) (X 0) with hG
  set η : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hη
  set Pm : ℕ → Prop := fun j => ∃ c, 0 < c ∧ 0 < R (a₀ - η j) c ∧ 0 < G (a₀ - η j) c
  set Pp : ℕ → Prop := fun j => ∃ c, 0 < c ∧ R (a₀ + η j) c < 0 ∧ G (a₀ + η j) c < 0
  classical
  set cm : ℕ → ℝ := fun j => if h : Pm j then h.choose else 1 with hcm
  set cp : ℕ → ℝ := fun j => if h : Pp j then h.choose else 1 with hcp
  have hcm_spec : ∀ j, Pm j → 0 < cm j ∧ 0 < R (a₀ - η j) (cm j) ∧ 0 < G (a₀ - η j) (cm j) :=
    fun j h => by simp only [hcm, dite_eq_left h]; exact h.choose_spec
  have hcp_spec : ∀ j, Pp j → 0 < cp j ∧ R (a₀ + η j) (cp j) < 0 ∧ G (a₀ + η j) (cp j) < 0 :=
    fun j h => by simp only [hcp, dite_eq_left h]; exact h.choose_spec
  have e1 := ae_all_rate (fun j => a₀ - η j) cm hmeas hpos hindep hident hint
  have e2 := ae_all_shape (fun j => a₀ - η j) cm hmeas hpos hindep hident hint hintS
  have e3 := ae_all_rate (fun j => a₀ + η j) cp hmeas hpos hindep hident hint
  have e4 := ae_all_shape (fun j => a₀ + η j) cp hmeas hpos hindep hident hint hintS
  have e5 := ae_all_rate (fun p : ℕ × ℕ => a₀ - η p.2) (fun p => b₀ - η p.1) hmeas hpos hindep
    hident hint
  have e6 := ae_all_rate (fun p : ℕ × ℕ => a₀ + η p.2) (fun p => b₀ + η p.1) hmeas hpos hindep
    hident hint
  filter_upwards [e1, e2, e3, e4, e5, e6] with ω h1 h2 h3 h4 h5 h6
  intro ε hε
  have hmS := (hmeas 0).1
  have hmX := (hmeas 0).2
  obtain ⟨i, hi⟩ := exists_nat_one_div_lt (lt_min hε hb₀)
  have hδi : η i < min ε b₀ := hi
  have hδ0 : 0 < η i := by positivity
  have hδε : η i < ε := lt_of_lt_of_le hδi (min_le_left _ _)
  have hδb : η i < b₀ := lt_of_lt_of_le hδi (min_le_right _ _)
  have hDm : 0 < R a₀ (b₀ - η i) := by
    have := popRateScoreLog_strictAnti (μ := μ) ha₀ (sub_pos.2 hδb) (sub_lt_self b₀ hδ0) hmS hmX
      (hpos 0) hint
    rw [← hR, hroot] at this; exact this
  have hDp : R a₀ (b₀ + η i) < 0 := by
    have := popRateScoreLog_strictAnti (μ := μ) ha₀ hb₀ (lt_add_of_pos_right b₀ hδ0) hmS hmX
      (hpos 0) hint
    rw [← hR, hroot] at this; exact this
  obtain ⟨u, hu, hu'⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hsign
  have hu0 : (0 : ℝ) < u := hu
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt
    (lt_min (lt_min hε hu0) (lt_min ha₀ (lt_min hDm (neg_pos.2 hDp))))
  have hj' : η j < min (min ε u) (min a₀ (min (R a₀ (b₀ - η i)) (-R a₀ (b₀ + η i)))) := hj
  have hη0 : 0 < η j := by positivity
  have hηε : η j < ε := lt_of_lt_of_le hj' ((min_le_left _ _).trans (min_le_left _ _))
  have hηu : η j < u := lt_of_lt_of_le hj' ((min_le_left _ _).trans (min_le_right _ _))
  have hηa : η j < a₀ := lt_of_lt_of_le hj' ((min_le_right _ _).trans (min_le_left _ _))
  have hηm : η j < R a₀ (b₀ - η i) := lt_of_lt_of_le hj'
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηp : η j < -R a₀ (b₀ + η i) := lt_of_lt_of_le hj'
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have ham : 0 < a₀ - η j := sub_pos.2 hηa
  have hap : 0 < a₀ + η j := by linarith
  obtain ⟨hPm, hPp⟩ := hu' ⟨hη0, hηu⟩
  obtain ⟨hcm0, hRm, hGm⟩ := hcm_spec j hPm
  obtain ⟨hcp0, hRp, hGp⟩ := hcp_spec j hPp
  -- the population rate scores at `b₀ ∓ η i` keep their sign at the shapes `a₀ ∓ η j`
  have hRm' : 0 < R (a₀ - η j) (b₀ - η i) := by
    have := abs_popRateScoreLog_sub_le (μ := μ) ham.le ha₀.le (sub_pos.2 hδb) hmS hmX (hpos 0)
      hint
    rw [← hR, show a₀ - η j - a₀ = -η j by ring, abs_neg, abs_of_pos hη0] at this
    linarith [(abs_le.1 this).1]
  have hRp' : R (a₀ + η j) (b₀ + η i) < 0 := by
    have := abs_popRateScoreLog_sub_le (μ := μ) (b := b₀ + η i) hap.le ha₀.le (by linarith) hmS
      hmX (hpos 0) hint
    rw [← hR, show a₀ + η j - a₀ = η j by ring, abs_of_pos hη0] at this
    linarith [(abs_le.1 this).2]
  filter_upwards [(h1 j ham hcm0).eventually (lt_mem_nhds hRm),
    (h2 j ham hcm0).eventually (lt_mem_nhds hGm),
    (h3 j hap hcp0).eventually (gt_mem_nhds hRp),
    (h4 j hap hcp0).eventually (gt_mem_nhds hGp),
    (h5 (i, j) ham (sub_pos.2 hδb)).eventually (lt_mem_nhds hRm'),
    (h6 (i, j) hap (by linarith)).eventually (gt_mem_nhds hRp')] with n n1 n2 n3 n4 n5 n6
  have hne : Nonempty (Fin n) := nonempty_fin_of_inv_mul_ne n1.ne'
  have hn0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.2 n.cast_nonneg
  have hsω : ∀ i : Fin n, 0 < S i ω := fun i => hpos i ω
  set s : Fin n → ℝ := fun i => S i ω
  set k : Fin n → ℕ := fun i => X i ω
  obtain ⟨hk, hrp⟩ := rateRoot_lt_of_rateScoreLog_neg hap hcp0 hsω (neg_of_mul_neg_right n3 hn0)
  have hrm := lt_rateRoot_of_rateScoreLog_pos ham hsω hk (pos_of_mul_pos_right n1 hn0)
  have hbm := lt_rateRoot_of_rateScoreLog_pos ham hsω hk (pos_of_mul_pos_right n5 hn0)
  obtain ⟨_, hbp⟩ := rateRoot_lt_of_rateScoreLog_neg hap (by linarith : 0 < b₀ + η i) hsω
    (neg_of_mul_neg_right n6 hn0)
  have hPm' : 0 < profileShapeScoreVarying (a₀ - η j) s k :=
    lt_of_lt_of_le (pos_of_mul_pos_right n2 hn0) (shapeScore_le_of_le hcm0 hrm.le hsω k)
  have hPp' : profileShapeScoreVarying (a₀ + η j) s k < 0 :=
    lt_of_le_of_lt (shapeScore_le_of_le (rateRoot_spec hap hsω hk).1 hrp.le hsω k)
      (neg_of_mul_neg_right n4 hn0)
  obtain ⟨a, ha, hPa⟩ := intermediate_value_Icc' (by linarith : a₀ - η j ≤ a₀ + η j)
    ((continuousOn_profileShapeScoreVarying hsω hk).mono fun x hx =>
      (by linarith [hx.1] : (0 : ℝ) < x)) ⟨hPp'.le, hPm'.le⟩
  have ha0 : 0 < a := by linarith [ha.1]
  have hb := (rateRoot_spec ha0 hsω hk).1
  have hmono := (rateRoot_strictMonoOn hsω hk).monotoneOn
  have hlo : rateRoot (a₀ - η j) s k ≤ rateRoot a s k :=
    hmono (Set.mem_Ioi.2 ham) (Set.mem_Ioi.2 ha0) ha.1
  have hhi : rateRoot a s k ≤ rateRoot (a₀ + η j) s k :=
    hmono (Set.mem_Ioi.2 ha0) (Set.mem_Ioi.2 hap) ha.2
  refine ⟨a, rateRoot a s k, ha0, hb, ?_, ?_, (score_eq_zero_iff_rateRoot ha0 hb hsω).2 ⟨rfl, hPa⟩⟩
  · exact lt_of_le_of_lt (abs_sub_le_iff.2 ⟨by linarith [ha.2], by linarith [ha.1]⟩) hηε
  · exact lt_of_lt_of_le (abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩) hδε.le

end Sampling

end MathlibExt.Biology.Omics.HierarchicalCount
