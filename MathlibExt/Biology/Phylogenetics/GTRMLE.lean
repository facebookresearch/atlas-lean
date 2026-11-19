/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.GTRIdentifiability
public import MathlibExt.Biology.Phylogenetics.GTRInference
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# GTR maximum likelihood: consistency by Wald's argument

This file proves that the **maximum-likelihood estimator** of the parameters of a GTR model
(more generally, of any continuous, everywhere-positive model of the site-pattern law) is
consistent, almost surely and in probability, up to the symmetries under which the model is
identified.

## Setting (source-frozen)

Chang (1996, §5, Theorem 5.1, via the Wald-type Lemma 5.1) derives almost-sure consistency of
the maximum-likelihood estimator of a Markov model on a tree from point identifiability, over
the closure of a bounded parameter space. Wald (1949) and Chang argue by a finite cover of
neighbourhoods together with the strong law of large numbers. This file instead uses the
uniform-LLN/argmax form of Newey–McFadden (1994, Theorem 2.1): the expected log-likelihood
`θ ↦ ∑ a, law θ₀ a * log (law θ a)` has a well-separated maximum at the identified class of
`θ₀` (the information inequality, their Lemma 2.2), and the average log-likelihood converges to
it uniformly in `θ`. The result is the finite-pattern case of their Theorem 2.5 (consistency of
maximum likelihood under identification, compactness, continuity and a dominance condition).

The setting is that of the minimum-distance corollary `GTRInference` (T67), whose empirical
frequencies and sampling-law results are reused:

* `Θ` is a **compact** metric parameter space (base frequencies, exchangeabilities and branch
  lengths in a closed box), `σ` the finite set of site patterns, and `law θ : σ → ℝ` the
  site-pattern law, assumed **continuous** in `θ`.
* **Positivity and normalization, as hypotheses**: `0 < law θ a` and `∑ a, law θ a = 1` for
  every `θ` and `a`. For GTR this holds when the frequencies are positive and the branch lengths
  are bounded away from `0` (at length `0` a branch forbids every pattern with different bases at
  its ends, see the JC69 boundary test). Positivity is stronger than both sources:
  Newey–McFadden's dominance condition only needs a lower bound on `law θ a` over `θ` for the
  patterns `a` in the support of `law θ₀`, and Chang needs none (he works over the closure of
  the parameter space). It is imposed here because of the convention `Real.log 0 = 0`, under
  which a model assigning probability `0` to an observed pattern would not be penalized.
* **Identifiability (the T66 input)** `hId`: there is a class `E ⊆ Θ` with
  `law θ = law θ₀ → θ ∈ E`, the parameters equivalent to `θ₀` under the permitted symmetries.
  For an arbitrary model `law` this is the identifiability statement itself, so the generic
  theorems take it as a hypothesis. For the **GTR pair-site model** `gtrLaw` (one branch; each
  `θ` gives base frequencies, exchangeabilities in the GTR domain and a branch length `t θ > 0`)
  it is proved, not assumed: `mem_gtrClass_of_gtrLaw_eq` derives it from T66's single-branch
  identifiability theorem `GTRIdentifiability.gtrPairLaw_eq_iff` (#1565), with `E = gtrClass`,
  the parameters with the same base frequencies and the same off-diagonal products
  `t * s i j`. The remaining symmetries are T66's: rate/time scaling and the unused diagonal of
  `s`. The `gtrClass` theorems below are the consistency results with this `hId`; their
  positivity and normalization hypotheses are discharged too.
* **Sampling law, as a hypothesis**: the alignment columns `X i : Ω → σ` are measurable,
  pairwise independent, identically distributed, and `P (X 0 = a) = law θ₀ a`.

The **uniform law of large numbers** for the log-likelihood is *proved*, not assumed: on a
finite pattern set the average log-likelihood is `logLik law (empiricalFreq X n ω)`, which is
Lipschitz in the frequencies uniformly in `θ` (`exists_abs_logLik_sub_logLik_le`), so the strong law
for the pattern frequencies gives almost-sure uniform convergence
(`ae_tendstoUniformly_logLik_empiricalFreq`).

The estimator is any `est n ω` maximizing `θ ↦ logLik law (empiricalFreq X n ω) θ`, the average
log-likelihood of the first `n` columns (`logLik_empiricalFreq`); a maximizer exists by
compactness (`mle`). The estimator need not be measurable: convergence in measure is stated
with the outer measure.

## Main definitions

* `logLik`: the log-likelihood criterion `∑ a, f a * log (law θ a)` of frequencies `f`.
* `IsMLE`: `est` maximizes the log-likelihood criterion of the frequency estimates.
* `mle`: a chosen maximum-likelihood estimator on a compact parameter space.

## Main results

* `exists_pos_add_le_of_identified`: an identified maximum of a continuous criterion on a
  compact space is well separated.
* `tendsto_infDist_of_tendstoUniformly`: **Wald's argmax argument**: maximizers of criteria
  converging uniformly to a criterion with an identified maximum converge to the identified
  class.
* `logLik_empiricalFreq`: the criterion at the empirical frequencies is the average
  log-likelihood of the sample.
* `logLik_lt_logLik_self`: the information (Gibbs) inequality, strict off the true law.
* `ae_tendstoUniformly_logLik_empiricalFreq`: the uniform law of large numbers.
* `ae_tendsto_infDist_mle`: **almost-sure consistency** of the GTR MLE up to the symmetries,
  a generalization of Chang's Lemma 5.1 from point identification to identification up to a
  class `E`.
* `tendstoInMeasure_infDist_mle`: consistency in probability (the T67 form).
* `ae_tendsto_mle_of_injective`: with full identifiability, `est n → θ₀` almost surely; the
  direct analogue of Chang's Lemma 5.1, under positivity.
* `tendstoInMeasure_mle_of_injective`: with full identifiability, `est n → θ₀` in probability.
* `mem_gtrClass_of_gtrLaw_eq`: **`hId` for the GTR pair-site model**, from T66
  (`gtrLaw_eq_iff_mem_gtrClass` is the exact form).
* `ae_tendsto_infDist_gtrClass_mle`, `tendstoInMeasure_infDist_gtrClass_mle`,
  `tendstoInMeasure_infDist_gtrClass_mleEstimator`,
  `ae_tendsto_mle_of_gtrClass_subset_singleton`,
  `tendstoInMeasure_mle_of_gtrClass_subset_singleton`: the consistency theorems for the GTR
  pair-site model, with `hId` supplied by T66.

## Scope

Rates of convergence, asymptotic normality, unbounded parameter spaces and boundary
parameters with zero-probability patterns are outside this file.

## References

* A. Wald, *Note on the consistency of the maximum likelihood estimate*, Annals of Mathematical
  Statistics 20 (1949), 595–601.
* J. T. Chang, *Full reconstruction of Markov models on evolutionary trees: identifiability and
  consistency*, Mathematical Biosciences 137 (1996), 51–73; §5, Theorem 5.1 (p. 70) and
  Lemma 5.1 (pp. 70–71).
* W. K. Newey and D. McFadden, *Large sample estimation and hypothesis testing*, Handbook of
  Econometrics, vol. 4, ch. 36, Elsevier, 1994, pp. 2111–2245; Theorem 2.1 (p. 2121),
  Lemma 2.2 (p. 2124) and Theorem 2.5 (p. 2131).
-/

@[expose] public section

open Filter Finset Function MeasureTheory ProbabilityTheory Metric Topology

namespace MathlibExt.Biology.Phylogenetics.GTRMLE

open MathlibExt.Biology.Phylogenetics.GTRInference

variable {Θ σ : Type*}

/-! ## The log-likelihood criterion and the estimator -/

/-- The **log-likelihood criterion** of the model `law` at frequencies `f`:
`∑ a, f a * log (law θ a)`. At the empirical frequencies of a sample it is the average
log-likelihood of the sample (`logLik_empiricalFreq`); at the true law `law θ₀` it is the
expected log-likelihood. -/
noncomputable def logLik [Fintype σ] (law : Θ → σ → ℝ) (f : σ → ℝ) (θ : Θ) : ℝ :=
  ∑ a, f a * Real.log (law θ a)

/-- `est` is a **maximum-likelihood estimator** for the model `law` given frequency estimates
`freq`: for every `n` and `ω`, `est n ω` maximizes `logLik law (freq n ω)` over the whole
parameter space. With `freq = empiricalFreq X` this is the MLE of the sample. -/
def IsMLE [Fintype σ] {Ω : Type*} (law : Θ → σ → ℝ) (freq : ℕ → Ω → σ → ℝ)
    (est : ℕ → Ω → Θ) : Prop :=
  ∀ n ω θ, logLik law (freq n ω) θ ≤ logLik law (freq n ω) (est n ω)

/-- **The criterion at the empirical frequencies is the average log-likelihood** of the first
`n` columns: `logLik law (empiricalFreq X n ω) θ = n⁻¹ * ∑ i < n, log (law θ (X i ω))`. -/
theorem logLik_empiricalFreq [Fintype σ] [DecidableEq σ] {Ω : Type*} (law : Θ → σ → ℝ)
    (X : ℕ → Ω → σ) (n : ℕ) (ω : Ω) (θ : Θ) :
    logLik law (empiricalFreq X n ω) θ =
      (n : ℝ)⁻¹ * ∑ i ∈ range n, Real.log (law θ (X i ω)) := by
  simp only [logLik, empiricalFreq, mul_assoc, ← mul_sum]
  congr 1
  rw [← sum_fiberwise (range n) (fun i => X i ω) fun i => Real.log (law θ (X i ω))]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_congr rfl fun i hi => by rw [(mem_filter.1 hi).2], sum_const, nsmul_eq_mul]

section Continuity

variable [TopologicalSpace Θ] [Fintype σ]

/-- The criterion is continuous in `θ` for a continuous, positive model. -/
theorem continuous_logLik {law : Θ → σ → ℝ} (hlaw : Continuous law)
    (hpos : ∀ θ a, 0 < law θ a) (f : σ → ℝ) : Continuous (logLik law f) :=
  continuous_finsetSum _ fun a _ =>
    continuous_const.mul (((continuous_apply a).comp hlaw).log fun θ => (hpos θ a).ne')

variable [CompactSpace Θ] [Nonempty Θ]

/-- A **maximum-likelihood estimator** on a nonempty compact parameter space with a continuous
positive model: a maximizer of `logLik law (freq n ω)`, chosen by the extreme value theorem. -/
noncomputable def mle {Ω : Type*} {law : Θ → σ → ℝ} (hlaw : Continuous law)
    (hpos : ∀ θ a, 0 < law θ a) (freq : ℕ → Ω → σ → ℝ) (n : ℕ) (ω : Ω) : Θ :=
  (isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (continuous_logLik hlaw hpos (freq n ω)).continuousOn).choose

/-- `mle` is a maximum-likelihood estimator. -/
theorem isMLE_mle {Ω : Type*} {law : Θ → σ → ℝ} (hlaw : Continuous law)
    (hpos : ∀ θ a, 0 < law θ a) (freq : ℕ → Ω → σ → ℝ) :
    IsMLE law freq (mle hlaw hpos freq) := fun n ω θ =>
  (isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (continuous_logLik hlaw hpos (freq n ω)).continuousOn).choose_spec.2 (Set.mem_univ θ)

end Continuity

/-! ## Wald's argmax argument (for an abstract criterion) -/

section Wald

variable [MetricSpace Θ]

/-- **An identified maximum is well separated on a compact space**: if `M` is continuous and
every `θ` with `M θ₀ ≤ M θ` lies in `E`, then for every `ε > 0` there is `δ > 0` with
`M θ + δ ≤ M θ₀` whenever `θ` is at distance at least `ε` from `E`. -/
theorem exists_pos_add_le_of_identified [CompactSpace Θ] {M : Θ → ℝ} (hM : Continuous M)
    {θ₀ : Θ} {E : Set Θ} (hId : ∀ θ, M θ₀ ≤ M θ → θ ∈ E) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ θ, ε ≤ infDist θ E → M θ + δ ≤ M θ₀ := by
  set K : Set Θ := {θ | ε ≤ infDist θ E}
  have hK : IsCompact K := (isClosed_le continuous_const (continuous_infDist_pt E)).isCompact
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, one_pos, fun θ hθ => ?_⟩
    exact absurd (show θ ∈ K from hθ) (hK0 ▸ Set.notMem_empty θ)
  obtain ⟨θ₁, hθ₁K, hθ₁⟩ := hK.exists_isMaxOn hKne hM.continuousOn
  have hlt : M θ₁ < M θ₀ := by
    by_contra h
    have h0 : infDist θ₁ E = 0 := infDist_zero_of_mem (hId θ₁ (not_lt.1 h))
    exact absurd (show ε ≤ infDist θ₁ E from hθ₁K) (by rw [h0]; exact not_le.2 hε)
  exact ⟨M θ₀ - M θ₁, sub_pos.2 hlt, fun θ hθ => by linarith [isMaxOn_iff.1 hθ₁ θ hθ]⟩

/-- **One step of Wald's argument**: if the maximum of `M` is separated by `δ` outside the
`ε`-neighbourhood of `E`, the criterion `Mn` is uniformly within `δ / 2` of `M`, and `θh` does at
least as well as `θ₀` for `Mn`, then `θh` is within `ε` of `E`. -/
theorem infDist_lt_of_forall_abs_sub_lt {M Mn : Θ → ℝ} {θ₀ θh : Θ} {E : Set Θ} {ε δ : ℝ}
    (hsep : ∀ θ, ε ≤ infDist θ E → M θ + δ ≤ M θ₀) (hunif : ∀ θ, |Mn θ - M θ| < δ / 2)
    (hmax : Mn θ₀ ≤ Mn θh) : infDist θh E < ε := by
  by_contra h
  have h1 := hsep θh (not_lt.1 h)
  have h2 := (abs_lt.1 (hunif θh)).2
  have h3 := (abs_lt.1 (hunif θ₀)).1
  linarith

/-- **Wald's argmax theorem** (Newey–McFadden, Theorem 2.1, deterministic core): if criteria
`Mn n` converge uniformly to a continuous `M` on a compact space whose maximum at `θ₀` is
identified up to `E`, then any maximizers `est n` of `Mn n` satisfy `infDist (est n) E → 0`. -/
theorem tendsto_infDist_of_tendstoUniformly [CompactSpace Θ] {M : Θ → ℝ} (hM : Continuous M)
    {θ₀ : Θ} {E : Set Θ} (hId : ∀ θ, M θ₀ ≤ M θ → θ ∈ E) {Mn : ℕ → Θ → ℝ}
    (hunif : TendstoUniformly Mn M atTop) {est : ℕ → Θ} (hest : ∀ n θ, Mn n θ ≤ Mn n (est n)) :
    Tendsto (fun n => infDist (est n) E) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_add_le_of_identified hM hId hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformly_iff.1 hunif (δ / 2) (half_pos hδ))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg infDist_nonneg]
  exact infDist_lt_of_forall_abs_sub_lt hsep
    (fun θ => by rw [abs_sub_comm, ← Real.dist_eq]; exact hN n hn θ) (hest n θ₀)

end Wald

/-! ## The information inequality -/

section Gibbs

variable [Fintype σ]

/-- **Information (Gibbs) inequality, strict form** (Newey–McFadden, Lemma 2.2): for a positive
normalized model, the expected log-likelihood under `law θ₀` is strictly smaller at every `θ`
whose law differs from `law θ₀`. -/
theorem logLik_lt_logLik_self {law : Θ → σ → ℝ} (hpos : ∀ θ a, 0 < law θ a)
    (hsum : ∀ θ, ∑ a, law θ a = 1) {θ₀ θ : Θ} (hne : law θ ≠ law θ₀) :
    logLik law (law θ₀) θ < logLik law (law θ₀) θ₀ := by
  set p := law θ₀
  set q := law θ
  have hterm : ∀ a, p a * Real.log (q a) - p a * Real.log (p a) ≤ q a - p a := fun a => by
    have := Real.log_le_sub_one_of_pos (div_pos (hpos θ a) (hpos θ₀ a))
    rw [Real.log_div (hpos θ a).ne' (hpos θ₀ a).ne'] at this
    have h := mul_le_mul_of_nonneg_left this (hpos θ₀ a).le
    rw [mul_sub, mul_sub, mul_div_cancel₀ _ (hpos θ₀ a).ne', mul_one] at h
    linarith
  obtain ⟨a₀, ha₀⟩ := Function.ne_iff.1 hne
  have hstrict : p a₀ * Real.log (q a₀) - p a₀ * Real.log (p a₀) < q a₀ - p a₀ := by
    have hne1 : q a₀ / p a₀ ≠ 1 := fun h => ha₀ ((div_eq_one_iff_eq (hpos θ₀ a₀).ne').1 h)
    have := Real.log_lt_sub_one_of_pos (div_pos (hpos θ a₀) (hpos θ₀ a₀)) hne1
    rw [Real.log_div (hpos θ a₀).ne' (hpos θ₀ a₀).ne'] at this
    have h := mul_lt_mul_of_pos_left this (hpos θ₀ a₀)
    rw [mul_sub, mul_sub, mul_div_cancel₀ _ (hpos θ₀ a₀).ne', mul_one] at h
    linarith
  have hlt : ∑ a, (p a * Real.log (q a) - p a * Real.log (p a)) < ∑ a, (q a - p a) :=
    sum_lt_sum (fun a _ => hterm a) ⟨a₀, mem_univ _, hstrict⟩
  rw [sum_sub_distrib, sum_sub_distrib, hsum θ, hsum θ₀, sub_self] at hlt
  simp only [logLik]
  linarith

/-- **Information inequality**: the expected log-likelihood under `law θ₀` is maximized at
`θ₀`. -/
theorem logLik_le_logLik_self {law : Θ → σ → ℝ} (hpos : ∀ θ a, 0 < law θ a)
    (hsum : ∀ θ, ∑ a, law θ a = 1) (θ₀ θ : Θ) :
    logLik law (law θ₀) θ ≤ logLik law (law θ₀) θ₀ := by
  by_cases h : law θ = law θ₀
  · exact le_of_eq (by simp only [logLik, h])
  · exact (logLik_lt_logLik_self hpos hsum h).le

/-- **Identification of the likelihood criterion**: if `law` identifies `θ₀` up to `E`, then
every maximizer of the expected log-likelihood `logLik law (law θ₀)` lies in `E`. -/
theorem mem_of_logLik_self_le {law : Θ → σ → ℝ} (hpos : ∀ θ a, 0 < law θ a)
    (hsum : ∀ θ, ∑ a, law θ a = 1) {θ₀ : Θ} {E : Set Θ} (hId : ∀ θ, law θ = law θ₀ → θ ∈ E)
    (θ : Θ) (hθ : logLik law (law θ₀) θ₀ ≤ logLik law (law θ₀) θ) : θ ∈ E := by
  by_contra hE
  exact absurd hθ (not_le.2 (logLik_lt_logLik_self hpos hsum fun h => hE (hId θ h)))

end Gibbs

/-! ## The uniform law of large numbers -/

section Uniform

variable [TopologicalSpace Θ] [CompactSpace Θ] [Fintype σ]

/-- **The criterion is Lipschitz in the frequencies, uniformly in `θ`**: for a continuous
positive model on a compact space there is `C ≥ 0` with
`|logLik law f θ - logLik law g θ| ≤ C * dist f g` for all `f`, `g`, `θ`. -/
theorem exists_abs_logLik_sub_logLik_le {law : Θ → σ → ℝ} (hlaw : Continuous law)
    (hpos : ∀ θ a, 0 < law θ a) :
    ∃ C, 0 ≤ C ∧ ∀ f g θ, |logLik law f θ - logLik law g θ| ≤ C * dist f g := by
  have hg : Continuous fun θ => fun a => Real.log (law θ a) :=
    continuous_pi fun a => ((continuous_apply a).comp hlaw).log fun θ => (hpos θ a).ne'
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨Fintype.card σ * |B|, by positivity, fun f g θ => ?_⟩
  have hlog : ∀ a, |Real.log (law θ a)| ≤ |B| := fun a =>
    ((norm_le_pi_norm (fun a => Real.log (law θ a)) a).trans (hB θ (Set.mem_univ θ))).trans
      (le_abs_self B)
  calc |logLik law f θ - logLik law g θ|
      = |∑ a, (f a - g a) * Real.log (law θ a)| := by
        simp only [logLik, ← sum_sub_distrib, sub_mul]
    _ ≤ ∑ a, |(f a - g a) * Real.log (law θ a)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : σ, dist f g * |B| := by
        refine sum_le_sum fun a _ => ?_
        rw [abs_mul, ← Real.dist_eq]
        exact mul_le_mul (dist_le_pi_dist f g a) (hlog a) (abs_nonneg _) dist_nonneg
    _ = Fintype.card σ * |B| * dist f g := by
        rw [sum_const, card_univ, nsmul_eq_mul]; ring

/-- **Uniform convergence of the criterion**: if the frequencies converge to `q`, the
log-likelihood criteria converge to `logLik law q` uniformly in `θ`. -/
theorem tendstoUniformly_logLik {law : Θ → σ → ℝ} (hlaw : Continuous law)
    (hpos : ∀ θ a, 0 < law θ a) {f : ℕ → σ → ℝ} {q : σ → ℝ} (hf : Tendsto f atTop (𝓝 q)) :
    TendstoUniformly (fun n => logLik law (f n)) (logLik law q) atTop := by
  obtain ⟨C, hC, hL⟩ := exists_abs_logLik_sub_logLik_le hlaw hpos
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hev := (Metric.tendsto_nhds.1 hf) (ε / (C + 1)) (div_pos hε (by linarith))
  filter_upwards [hev] with n hn θ
  rw [Real.dist_eq, abs_sub_comm]
  calc |logLik law (f n) θ - logLik law q θ| ≤ C * dist (f n) q := hL _ _ _
    _ ≤ (C + 1) * dist (f n) q := by gcongr; linarith
    _ < (C + 1) * (ε / (C + 1)) := by gcongr
    _ = ε := by field_simp

variable [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ] {Ω : Type*}
  [MeasurableSpace Ω] {P : Measure Ω}

/-- **Uniform law of large numbers for the log-likelihood**: under the sampling law, the
average log-likelihood `logLik law (empiricalFreq X n ω)` converges to the expected
log-likelihood `logLik law (law θ₀)` uniformly in `θ`, for almost every `ω`. -/
theorem ae_tendstoUniformly_logLik_empiricalFreq [IsFiniteMeasure P] {law : Θ → σ → ℝ}
    (hlaw : Continuous law) (hpos : ∀ θ a, 0 < law θ a) {θ₀ : Θ} {X : ℕ → Ω → σ}
    (hX : ∀ i, Measurable (X i)) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = law θ₀ a) :
    ∀ᵐ ω ∂P, TendstoUniformly (fun n => logLik law (empiricalFreq X n ω)) (logLik law (law θ₀))
      atTop := by
  filter_upwards [ae_tendsto_empiricalFreq hX hindep hident hsample] with ω hω
  exact tendstoUniformly_logLik hlaw hpos hω

end Uniform

/-! ## Consistency of the maximum-likelihood estimator -/

section Consistency

variable [MetricSpace Θ] [CompactSpace Θ] [Fintype σ]

/-- **Deterministic consistency**: along any sequence of frequencies converging to `law θ₀`,
maximizers of the log-likelihood criterion approach the identified class `E`. -/
theorem tendsto_infDist_of_tendsto_freq {law : Θ → σ → ℝ} (hlaw : Continuous law)
    (hpos : ∀ θ a, 0 < law θ a) (hsum : ∀ θ, ∑ a, law θ a = 1) {θ₀ : Θ} {E : Set Θ}
    (hId : ∀ θ, law θ = law θ₀ → θ ∈ E) {f : ℕ → σ → ℝ} (hf : Tendsto f atTop (𝓝 (law θ₀)))
    {est : ℕ → Θ} (hest : ∀ n θ, logLik law (f n) θ ≤ logLik law (f n) (est n)) :
    Tendsto (fun n => infDist (est n) E) atTop (𝓝 0) :=
  tendsto_infDist_of_tendstoUniformly (continuous_logLik hlaw hpos _)
    (mem_of_logLik_self_le hpos hsum hId) (tendstoUniformly_logLik hlaw hpos hf) hest

/-- **Quantitative separation for the MLE**: for every `ε > 0` there is `η > 0` such that any
maximizer of `logLik law f` with `dist f (law θ₀) < η` lies within `ε` of `E`. -/
theorem exists_pos_infDist_lt_of_dist_lt {law : Θ → σ → ℝ} (hlaw : Continuous law)
    (hpos : ∀ θ a, 0 < law θ a) (hsum : ∀ θ, ∑ a, law θ a = 1) {θ₀ : Θ} {E : Set Θ}
    (hId : ∀ θ, law θ = law θ₀ → θ ∈ E) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ (f : σ → ℝ) (θh : Θ), dist f (law θ₀) < η →
      (∀ θ, logLik law f θ ≤ logLik law f θh) → infDist θh E < ε := by
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_add_le_of_identified (continuous_logLik hlaw hpos (law θ₀))
    (mem_of_logLik_self_le hpos hsum hId) hε
  obtain ⟨C, hC, hL⟩ := exists_abs_logLik_sub_logLik_le hlaw hpos
  refine ⟨δ / 2 / (C + 1), div_pos (half_pos hδ) (by linarith), fun f θh hf hmax => ?_⟩
  refine infDist_lt_of_forall_abs_sub_lt hsep (fun θ => ?_) (hmax θ₀)
  calc |logLik law f θ - logLik law (law θ₀) θ| ≤ C * dist f (law θ₀) := hL _ _ _
    _ ≤ (C + 1) * dist f (law θ₀) := by gcongr; linarith
    _ < (C + 1) * (δ / 2 / (C + 1)) := by gcongr
    _ = δ / 2 := by field_simp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Consistency in probability from convergent frequencies**: if `law` identifies `θ₀` up to
`E` and the frequency estimates converge in probability to `law θ₀`, then every
maximum-likelihood estimator satisfies `infDist (est n) E → 0` in probability. -/
theorem tendstoInMeasure_infDist_mle_of_tendstoInMeasure {law : Θ → σ → ℝ}
    (hlaw : Continuous law) (hpos : ∀ θ a, 0 < law θ a) (hsum : ∀ θ, ∑ a, law θ a = 1)
    {θ₀ : Θ} {E : Set Θ} (hId : ∀ θ, law θ = law θ₀ → θ ∈ E) {freq : ℕ → Ω → σ → ℝ}
    {est : ℕ → Ω → Θ} (hest : IsMLE law freq est)
    (hfreq : TendstoInMeasure P freq atTop fun _ => law θ₀) :
    TendstoInMeasure P (fun n ω => infDist (est n ω) E) atTop fun _ => 0 := by
  rw [tendstoInMeasure_iff_dist] at hfreq ⊢
  intro ε hε
  obtain ⟨η, hη, hsep⟩ := exists_pos_infDist_lt_of_dist_lt hlaw hpos hsum hId hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hfreq η hη)
    (fun _ => bot_le) fun n => measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg infDist_nonneg] at hω ⊢
  by_contra h
  exact absurd (hsep _ _ (not_le.1 h) (hest n ω)) (not_lt.2 hω)

variable [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ] [IsFiniteMeasure P]

/-- **Almost-sure consistency of the GTR maximum-likelihood estimator**, a generalization of
Chang's Lemma 5.1 from point identification to identification up to a class `E`
(Newey–McFadden, Theorem 2.5, finite-pattern case). Let `Θ` be compact, `law` continuous,
positive and normalized, and `θ₀` identified up to the class `E` (`hId`, the T66 input). If the
alignment columns are pairwise independent and identically distributed with
`P (X 0 = a) = law θ₀ a`, every MLE `est` satisfies `infDist (est n ω) E → 0` for almost
every `ω`. -/
theorem ae_tendsto_infDist_mle {law : Θ → σ → ℝ} (hlaw : Continuous law)
    (hpos : ∀ θ a, 0 < law θ a) (hsum : ∀ θ, ∑ a, law θ a = 1) {θ₀ : Θ} {E : Set Θ}
    (hId : ∀ θ, law θ = law θ₀ → θ ∈ E) {X : ℕ → Ω → σ} (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = law θ₀ a) {est : ℕ → Ω → Θ}
    (hest : IsMLE law (empiricalFreq X) est) :
    ∀ᵐ ω ∂P, Tendsto (fun n => infDist (est n ω) E) atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_empiricalFreq hX hindep hident hsample] with ω hω
  exact tendsto_infDist_of_tendsto_freq hlaw hpos hsum hId hω fun n θ => hest n ω θ

/-- **Consistency in probability of the GTR maximum-likelihood estimator**, up to the permitted
symmetries, under the hypotheses of `ae_tendsto_infDist_mle`. The estimator need not be
measurable. -/
theorem tendstoInMeasure_infDist_mle {law : Θ → σ → ℝ} (hlaw : Continuous law)
    (hpos : ∀ θ a, 0 < law θ a) (hsum : ∀ θ, ∑ a, law θ a = 1) {θ₀ : Θ} {E : Set Θ}
    (hId : ∀ θ, law θ = law θ₀ → θ ∈ E) {X : ℕ → Ω → σ} (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = law θ₀ a) {est : ℕ → Ω → Θ}
    (hest : IsMLE law (empiricalFreq X) est) :
    TendstoInMeasure P (fun n ω => infDist (est n ω) E) atTop fun _ => 0 :=
  tendstoInMeasure_infDist_mle_of_tendstoInMeasure hlaw hpos hsum hId hest
    (tendstoInMeasure_empiricalFreq hX hindep hident hsample)

/-- The GTR MLE consistency theorem (in probability) for the chosen estimator `mle`. -/
theorem tendstoInMeasure_infDist_mleEstimator [Nonempty Θ] {law : Θ → σ → ℝ}
    (hlaw : Continuous law) (hpos : ∀ θ a, 0 < law θ a) (hsum : ∀ θ, ∑ a, law θ a = 1)
    {θ₀ : Θ} {E : Set Θ} (hId : ∀ θ, law θ = law θ₀ → θ ∈ E) {X : ℕ → Ω → σ}
    (hX : ∀ i, Measurable (X i)) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = law θ₀ a) :
    TendstoInMeasure P (fun n ω => infDist (mle hlaw hpos (empiricalFreq X) n ω) E) atTop
      fun _ => 0 :=
  tendstoInMeasure_infDist_mle hlaw hpos hsum hId hX hindep hident hsample (isMLE_mle hlaw hpos _)

/-- **Full identifiability, almost surely**: if `law` is injective at `θ₀`, every MLE converges
to `θ₀` almost surely. This is the direct analogue of Chang's Lemma 5.1, under the positivity
hypothesis `hpos`. -/
theorem ae_tendsto_mle_of_injective {law : Θ → σ → ℝ} (hlaw : Continuous law)
    (hpos : ∀ θ a, 0 < law θ a) (hsum : ∀ θ, ∑ a, law θ a = 1) {θ₀ : Θ}
    (hId : ∀ θ, law θ = law θ₀ → θ = θ₀) {X : ℕ → Ω → σ} (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = law θ₀ a) {est : ℕ → Ω → Θ}
    (hest : IsMLE law (empiricalFreq X) est) :
    ∀ᵐ ω ∂P, Tendsto (fun n => est n ω) atTop (𝓝 θ₀) := by
  filter_upwards [ae_tendsto_infDist_mle hlaw hpos hsum (E := {θ₀}) hId hX hindep hident hsample
    hest] with ω hω
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [infDist_singleton] using hω

/-- **Full identifiability, in probability**: if `law` is injective at `θ₀`, every MLE
converges to `θ₀` in probability. -/
theorem tendstoInMeasure_mle_of_injective {law : Θ → σ → ℝ} (hlaw : Continuous law)
    (hpos : ∀ θ a, 0 < law θ a) (hsum : ∀ θ, ∑ a, law θ a = 1) {θ₀ : Θ}
    (hId : ∀ θ, law θ = law θ₀ → θ = θ₀) {X : ℕ → Ω → σ} (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = law θ₀ a) {est : ℕ → Ω → Θ}
    (hest : IsMLE law (empiricalFreq X) est) :
    TendstoInMeasure P est atTop fun _ => θ₀ := by
  have h := tendstoInMeasure_infDist_mle hlaw hpos hsum (E := {θ₀}) hId hX hindep hident hsample
    hest
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  simpa [infDist_singleton] using h ε hε

end Consistency

/-! ## The GTR pair-site model: `hId` from GTR identifiability (T66) -/

section GTRPairSite

open GTRIdentifiability SubstitutionModels

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **GTR pair-site model**: the parameter `θ` gives base frequencies `π θ`,
exchangeabilities `s θ` and a branch length `t θ`, and the law of an aligned site pattern
`(i, j)` for two taxa is T66's pair-site law `gtrPairLaw (π θ) (s θ) (t θ) i j`. -/
noncomputable def gtrLaw (π : Θ → ι → ℝ) (s : Θ → Matrix ι ι ℝ) (t : Θ → ℝ) (θ : Θ) :
    ι × ι → ℝ :=
  fun a => gtrPairLaw (π θ) (s θ) (t θ) a.1 a.2

/-- The **identified class** of `θ₀` in the GTR pair-site model: the parameters with the same
base frequencies and the same off-diagonal products `t * s i j` (T66's permitted symmetries at
one branch: rate/time scaling and the unused diagonal of `s`). -/
def gtrClass (π : Θ → ι → ℝ) (s : Θ → Matrix ι ι ℝ) (t : Θ → ℝ) (θ₀ : Θ) : Set Θ :=
  {θ | π θ = π θ₀ ∧ ∀ i j, i ≠ j → t θ * s θ i j = t θ₀ * s θ₀ i j}

variable {π : Θ → ι → ℝ} {s : Θ → Matrix ι ι ℝ} {t : Θ → ℝ}

/-- **Identifiability of the GTR pair-site model, exact form** (T66's
`gtrPairLaw_eq_iff`): on the GTR domain with positive branch lengths, two parameters have the
same law iff they lie in the same `gtrClass`. -/
theorem gtrLaw_eq_iff_mem_gtrClass (hp : ∀ θ, IsGTRParam (π θ) (s θ)) (ht : ∀ θ, 0 < t θ)
    (θ₀ θ : Θ) : gtrLaw π s t θ = gtrLaw π s t θ₀ ↔ θ ∈ gtrClass π s t θ₀ := by
  change _ ↔ π θ = π θ₀ ∧ ∀ i j, i ≠ j → t θ * s θ i j = t θ₀ * s θ₀ i j
  rw [← gtrPairLaw_eq_iff (hp θ) (hp θ₀) (ht θ) (ht θ₀)]
  exact ⟨fun h => funext fun i => funext fun j => congrFun h (i, j),
    fun h => funext fun a => by simp only [gtrLaw, h]⟩

/-- **`hId` for the GTR pair-site model**, from T66: every parameter with the law of `θ₀` lies
in the identified class `gtrClass π s t θ₀`. This is the hypothesis `hId` of the generic
consistency theorems, discharged by `GTRIdentifiability.gtrPairLaw_eq_iff`. -/
theorem mem_gtrClass_of_gtrLaw_eq (hp : ∀ θ, IsGTRParam (π θ) (s θ)) (ht : ∀ θ, 0 < t θ)
    (θ₀ : Θ) : ∀ θ, gtrLaw π s t θ = gtrLaw π s t θ₀ → θ ∈ gtrClass π s t θ₀ :=
  fun θ => (gtrLaw_eq_iff_mem_gtrClass hp ht θ₀ θ).1

/-- The GTR pair-site law is positive for positive branch lengths. -/
theorem gtrLaw_pos (hp : ∀ θ, IsGTRParam (π θ) (s θ)) (ht : ∀ θ, 0 < t θ) (θ : Θ)
    (a : ι × ι) : 0 < gtrLaw π s t θ a :=
  mul_pos ((hp θ).pos a.1) ((isRateMatrix_gtrRate (fun k => ((hp θ).pos k).le)
    fun i j h => ((hp θ).offDiag_pos i j h).le).ctmcTransition_pos
      (fun i j h => by
        rw [gtrRate_apply_of_ne _ _ h]
        exact mul_pos ((hp θ).offDiag_pos i j h) ((hp θ).pos j))
      (ht θ) a.1 a.2)

/-- The GTR pair-site law is normalized. -/
theorem sum_gtrLaw (hp : ∀ θ, IsGTRParam (π θ) (s θ)) (θ : Θ) : ∑ a, gtrLaw π s t θ a = 1 := by
  rw [Fintype.sum_prod_type]
  exact sum_sum_gtrPairLaw (hp θ) (t θ)

/-- `mem_of_logLik_self_le` for the GTR pair-site model, with `hId` from T66. -/
theorem mem_gtrClass_of_logLik_self_le (hp : ∀ θ, IsGTRParam (π θ) (s θ)) (ht : ∀ θ, 0 < t θ)
    {θ₀ : Θ} (θ : Θ)
    (hθ : logLik (gtrLaw π s t) (gtrLaw π s t θ₀) θ₀ ≤
      logLik (gtrLaw π s t) (gtrLaw π s t θ₀) θ) : θ ∈ gtrClass π s t θ₀ :=
  mem_of_logLik_self_le (gtrLaw_pos hp ht) (sum_gtrLaw hp) (mem_gtrClass_of_gtrLaw_eq hp ht θ₀)
    θ hθ

variable [MetricSpace Θ] [CompactSpace Θ]

/-- `tendsto_infDist_of_tendsto_freq` for the GTR pair-site model, with `hId` from T66. -/
theorem tendsto_infDist_gtrClass_of_tendsto_freq (hlaw : Continuous (gtrLaw π s t))
    (hp : ∀ θ, IsGTRParam (π θ) (s θ)) (ht : ∀ θ, 0 < t θ) {θ₀ : Θ} {f : ℕ → ι × ι → ℝ}
    (hf : Tendsto f atTop (𝓝 (gtrLaw π s t θ₀))) {est : ℕ → Θ}
    (hest : ∀ n θ, logLik (gtrLaw π s t) (f n) θ ≤ logLik (gtrLaw π s t) (f n) (est n)) :
    Tendsto (fun n => infDist (est n) (gtrClass π s t θ₀)) atTop (𝓝 0) :=
  tendsto_infDist_of_tendsto_freq hlaw (gtrLaw_pos hp ht) (sum_gtrLaw hp)
    (mem_gtrClass_of_gtrLaw_eq hp ht θ₀) hf hest

/-- `exists_pos_infDist_lt_of_dist_lt` for the GTR pair-site model, with `hId` from T66. -/
theorem exists_pos_infDist_gtrClass_lt_of_dist_lt (hlaw : Continuous (gtrLaw π s t))
    (hp : ∀ θ, IsGTRParam (π θ) (s θ)) (ht : ∀ θ, 0 < t θ) {θ₀ : Θ} {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ (f : ι × ι → ℝ) (θh : Θ), dist f (gtrLaw π s t θ₀) < η →
      (∀ θ, logLik (gtrLaw π s t) f θ ≤ logLik (gtrLaw π s t) f θh) →
        infDist θh (gtrClass π s t θ₀) < ε :=
  exists_pos_infDist_lt_of_dist_lt hlaw (gtrLaw_pos hp ht) (sum_gtrLaw hp)
    (mem_gtrClass_of_gtrLaw_eq hp ht θ₀) hε

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `tendstoInMeasure_infDist_mle_of_tendstoInMeasure` for the GTR pair-site model, with `hId`
from T66. -/
theorem tendstoInMeasure_infDist_gtrClass_mle_of_tendstoInMeasure
    (hlaw : Continuous (gtrLaw π s t)) (hp : ∀ θ, IsGTRParam (π θ) (s θ)) (ht : ∀ θ, 0 < t θ)
    {θ₀ : Θ} {freq : ℕ → Ω → ι × ι → ℝ} {est : ℕ → Ω → Θ} (hest : IsMLE (gtrLaw π s t) freq est)
    (hfreq : TendstoInMeasure P freq atTop fun _ => gtrLaw π s t θ₀) :
    TendstoInMeasure P (fun n ω => infDist (est n ω) (gtrClass π s t θ₀)) atTop fun _ => 0 :=
  tendstoInMeasure_infDist_mle_of_tendstoInMeasure hlaw (gtrLaw_pos hp ht) (sum_gtrLaw hp)
    (mem_gtrClass_of_gtrLaw_eq hp ht θ₀) hest hfreq

variable [MeasurableSpace (ι × ι)] [MeasurableSingletonClass (ι × ι)] [IsFiniteMeasure P]

/-- **Almost-sure consistency of the GTR pair-site MLE**: `ae_tendsto_infDist_mle` with `hId`
from T66 (`mem_gtrClass_of_gtrLaw_eq`) and with positivity and normalization discharged. Every
MLE approaches the identified class `gtrClass π s t θ₀` almost surely. -/
theorem ae_tendsto_infDist_gtrClass_mle (hlaw : Continuous (gtrLaw π s t))
    (hp : ∀ θ, IsGTRParam (π θ) (s θ)) (ht : ∀ θ, 0 < t θ) {θ₀ : Θ} {X : ℕ → Ω → ι × ι}
    (hX : ∀ i, Measurable (X i)) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = gtrLaw π s t θ₀ a) {est : ℕ → Ω → Θ}
    (hest : IsMLE (gtrLaw π s t) (empiricalFreq X) est) :
    ∀ᵐ ω ∂P, Tendsto (fun n => infDist (est n ω) (gtrClass π s t θ₀)) atTop (𝓝 0) :=
  ae_tendsto_infDist_mle hlaw (gtrLaw_pos hp ht) (sum_gtrLaw hp)
    (mem_gtrClass_of_gtrLaw_eq hp ht θ₀) hX hindep hident hsample hest

/-- **Consistency in probability of the GTR pair-site MLE**: `tendstoInMeasure_infDist_mle`
with `hId` from T66. -/
theorem tendstoInMeasure_infDist_gtrClass_mle (hlaw : Continuous (gtrLaw π s t))
    (hp : ∀ θ, IsGTRParam (π θ) (s θ)) (ht : ∀ θ, 0 < t θ) {θ₀ : Θ} {X : ℕ → Ω → ι × ι}
    (hX : ∀ i, Measurable (X i)) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = gtrLaw π s t θ₀ a) {est : ℕ → Ω → Θ}
    (hest : IsMLE (gtrLaw π s t) (empiricalFreq X) est) :
    TendstoInMeasure P (fun n ω => infDist (est n ω) (gtrClass π s t θ₀)) atTop fun _ => 0 :=
  tendstoInMeasure_infDist_mle hlaw (gtrLaw_pos hp ht) (sum_gtrLaw hp)
    (mem_gtrClass_of_gtrLaw_eq hp ht θ₀) hX hindep hident hsample hest

/-- `tendstoInMeasure_infDist_mleEstimator` for the GTR pair-site model, with `hId` from T66. -/
theorem tendstoInMeasure_infDist_gtrClass_mleEstimator [Nonempty Θ]
    (hlaw : Continuous (gtrLaw π s t)) (hp : ∀ θ, IsGTRParam (π θ) (s θ)) (ht : ∀ θ, 0 < t θ)
    {θ₀ : Θ} {X : ℕ → Ω → ι × ι} (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = gtrLaw π s t θ₀ a) :
    TendstoInMeasure P
      (fun n ω => infDist (mle hlaw (gtrLaw_pos hp ht) (empiricalFreq X) n ω)
        (gtrClass π s t θ₀)) atTop fun _ => 0 :=
  tendstoInMeasure_infDist_mleEstimator hlaw (gtrLaw_pos hp ht) (sum_gtrLaw hp)
    (mem_gtrClass_of_gtrLaw_eq hp ht θ₀) hX hindep hident hsample

/-- **Point consistency of the GTR pair-site MLE, almost surely**: if the parametrization
separates the T66 invariants at `θ₀` (`gtrClass π s t θ₀ ⊆ {θ₀}`, e.g. a known branch length
and injective `(π, s)` off the diagonal), every MLE converges to `θ₀` almost surely.
`ae_tendsto_mle_of_injective` with its `hId` from T66. -/
theorem ae_tendsto_mle_of_gtrClass_subset_singleton (hlaw : Continuous (gtrLaw π s t))
    (hp : ∀ θ, IsGTRParam (π θ) (s θ)) (ht : ∀ θ, 0 < t θ) {θ₀ : Θ}
    (hsep : gtrClass π s t θ₀ ⊆ {θ₀}) {X : ℕ → Ω → ι × ι} (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = gtrLaw π s t θ₀ a) {est : ℕ → Ω → Θ}
    (hest : IsMLE (gtrLaw π s t) (empiricalFreq X) est) :
    ∀ᵐ ω ∂P, Tendsto (fun n => est n ω) atTop (𝓝 θ₀) :=
  ae_tendsto_mle_of_injective hlaw (gtrLaw_pos hp ht) (sum_gtrLaw hp)
    (fun θ h => hsep (mem_gtrClass_of_gtrLaw_eq hp ht θ₀ θ h)) hX hindep hident hsample hest

/-- **Point consistency of the GTR pair-site MLE, in probability**:
`tendstoInMeasure_mle_of_injective` with its `hId` from T66. -/
theorem tendstoInMeasure_mle_of_gtrClass_subset_singleton (hlaw : Continuous (gtrLaw π s t))
    (hp : ∀ θ, IsGTRParam (π θ) (s θ)) (ht : ∀ θ, 0 < t θ) {θ₀ : Θ}
    (hsep : gtrClass π s t θ₀ ⊆ {θ₀}) {X : ℕ → Ω → ι × ι} (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = gtrLaw π s t θ₀ a) {est : ℕ → Ω → Θ}
    (hest : IsMLE (gtrLaw π s t) (empiricalFreq X) est) :
    TendstoInMeasure P est atTop fun _ => θ₀ :=
  tendstoInMeasure_mle_of_injective hlaw (gtrLaw_pos hp ht) (sum_gtrLaw hp)
    (fun θ h => hsep (mem_gtrClass_of_gtrLaw_eq hp ht θ₀ θ h)) hX hindep hident hsample hest

end GTRPairSite

end MathlibExt.Biology.Phylogenetics.GTRMLE
