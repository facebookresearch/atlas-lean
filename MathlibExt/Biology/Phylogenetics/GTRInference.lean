/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.Order.Compact

/-!
# GTR inference: identifiability and the sampling law imply consistency

This file proves the inference corollary that follows a GTR identifiability theorem: if the
site-pattern law determines the GTR parameters up to the permitted symmetries, and alignment
columns are sampled independently from that law, then the **minimum-distance estimator** of the
parameters is consistent, up to the same symmetries.

## Setting (source-frozen)

The source is Chang (1996), where identifiability of a Markov model on a tree from the
joint law of the leaf states yields consistency of an estimator that matches the empirical
site-pattern frequencies to the model's law, on a compact parameter space; the abstract
argument is the basic consistency theorem for extremum estimators (Newey–McFadden 1994,
Theorem 2.1: identification, compactness, continuity, uniform convergence of the criterion).

* `Θ` is the GTR parameter space (base frequencies, exchangeabilities, branch lengths, and the
  tree topology if it is a parameter), as a **compact** metric space. Compactness is the usual
  restriction to a closed and bounded box of rates and branch lengths away from saturation.
* `σ` is the finite set of site patterns (for `m` taxa on the nucleotides, `Fin m → Fin 4`), and
  `law θ : σ → ℝ` is the site-pattern law of the model with parameter `θ`, assumed
  **continuous** in `θ` (true for GTR: the law is a polynomial in the entries of the transition
  matrices `exp (t • gtrRate π s)` and the frequencies `π`).
* **Identifiability (the T66 input), as a hypothesis**: there is a set `E ⊆ Θ`, the class of
  parameters equivalent to the true `θ₀` under the permitted label/state symmetries, with
  `law θ = law θ₀ → θ ∈ E`. Its proof is the content of the GTR identifiability theorem
  (PHY-02.2) and is not repeated here; nothing about its form is assumed beyond this
  implication, so the full-identifiability case is `E = {θ₀}`.
* **Sampling law, as a hypothesis**: the alignment columns `X i : Ω → σ` are pairwise independent,
  identically distributed, and `P (X 0 = a) = law θ₀ a`.

The estimator is any `est n ω` that minimizes `θ ↦ dist (law θ) (empiricalFreq X n ω)`, the
sup-distance between the model law and the empirical site-pattern frequencies after `n`
columns (`IsMinDistEstimator`; a minimizer exists by compactness, `minDistEstimator`). The
estimator need not be measurable: convergence in measure is stated with the outer measure.

Consistency is **up to the permitted symmetries**: the distance from `est n` to the class `E`
tends to `0` in probability. Identifiability is what makes this a statement about `θ₀` rather
than about the whole fibre `{θ | law θ = law θ₀}`; without it the same proof gives convergence
to that fibre only (`tendstoInMeasure_infDist_fiber`).

## Main definitions

* `empiricalFreq`: the empirical site-pattern frequencies of the first `n` columns.
* `IsMinDistEstimator`: `est` minimizes the distance between the model law and the empirical
  frequencies.
* `minDistEstimator`: a chosen minimum-distance estimator on a compact parameter space.

## Main results

* `exists_pos_le_dist_law`: identification is well separated on a compact space: parameters at
  distance at least `ε` from the fibre of `θ₀` have laws at distance at least `δ > 0` from
  `law θ₀`.
* `tendstoInMeasure_empiricalFreq`: the sampling law gives `empiricalFreq X n → law θ₀` in
  probability (via the strong law of large numbers).
* `tendstoInMeasure_infDist_of_tendstoInMeasure`: consistency from any convergent frequency
  estimate.
* `tendstoInMeasure_infDist_minDist`: **GTR inference corollary**: identifiability up to `E`
  and the sampling law imply `infDist (est n) E → 0` in probability.
* `tendstoInMeasure_minDist_of_injective`: with full identifiability, `est n → θ₀` in probability.

## Scope

General GTR rate-matrix estimation (likelihood-based estimators, rates of convergence,
asymptotic normality, unbounded parameter spaces) is outside this corollary.

## References

* J. T. Chang, *Full reconstruction of Markov models on evolutionary trees: identifiability and
  consistency*, Mathematical Biosciences 137 (1996), 51–73.
* W. K. Newey and D. McFadden, *Large sample estimation and hypothesis testing*, Handbook of
  Econometrics, vol. 4, ch. 36, Elsevier, 1994, pp. 2111–2245.
-/

@[expose] public section

open Filter Finset Function MeasureTheory ProbabilityTheory Metric Topology

namespace MathlibExt.Biology.Phylogenetics.GTRInference

variable {Θ σ : Type*}

/-! ## The estimator -/

/-- The **empirical site-pattern frequencies** of the first `n` alignment columns `X 0, …,
X (n - 1)`: the fraction of columns showing pattern `a`. At `n = 0` it is `0`. -/
noncomputable def empiricalFreq [DecidableEq σ] {Ω : Type*} (X : ℕ → Ω → σ) (n : ℕ) (ω : Ω) :
    σ → ℝ :=
  fun a => (n : ℝ)⁻¹ * (#{i ∈ range n | X i ω = a} : ℕ)

/-- `est` is a **minimum-distance estimator** for the model `law` given frequency estimates `freq`:
for every `n` and `ω`, `est n ω` minimizes `θ ↦ dist (law θ) (freq n ω)` over the whole parameter
space. With `freq = empiricalFreq X` this is the estimator of the GTR corollary. -/
def IsMinDistEstimator [Fintype σ] {Ω : Type*} (law : Θ → σ → ℝ) (freq : ℕ → Ω → σ → ℝ)
    (est : ℕ → Ω → Θ) : Prop :=
  ∀ n ω θ, dist (law (est n ω)) (freq n ω) ≤ dist (law θ) (freq n ω)

section Compact

variable [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [Fintype σ]

/-- A **minimum-distance estimator** on a nonempty compact parameter space with a continuous
model `law`: a minimizer of `θ ↦ dist (law θ) (freq n ω)`, chosen by the extreme value theorem. -/
noncomputable def minDistEstimator {Ω : Type*} {law : Θ → σ → ℝ} (hlaw : Continuous law)
    (freq : ℕ → Ω → σ → ℝ) (n : ℕ) (ω : Ω) : Θ :=
  (isCompact_univ.exists_isMinOn Set.univ_nonempty
    (hlaw.dist continuous_const).continuousOn (f := fun θ => dist (law θ) (freq n ω))).choose

/-- `minDistEstimator` is a minimum-distance estimator. -/
theorem isMinDistEstimator_minDistEstimator {Ω : Type*} {law : Θ → σ → ℝ}
    (hlaw : Continuous law) (freq : ℕ → Ω → σ → ℝ) :
    IsMinDistEstimator law freq (minDistEstimator hlaw freq) := fun n ω θ =>
  (isCompact_univ.exists_isMinOn Set.univ_nonempty
    (hlaw.dist continuous_const).continuousOn (f := fun θ => dist (law θ) (freq n ω))).choose_spec.2
    (Set.mem_univ θ)

end Compact

/-! ## Well-separated identification -/

section Separation

variable [MetricSpace Θ] [CompactSpace Θ] [Fintype σ]

/-- **Identification is well separated on a compact parameter space**: if `law` is continuous,
then for every `ε > 0` there is `δ > 0` such that every parameter at distance at least `ε` from
the fibre `{θ | law θ = law θ₀}` has a law at distance at least `δ` from `law θ₀`. -/
theorem exists_pos_le_dist_law {law : Θ → σ → ℝ} (hlaw : Continuous law) (θ₀ : Θ) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ θ, ε ≤ infDist θ {θ' | law θ' = law θ₀} →
      δ ≤ dist (law θ) (law θ₀) := by
  set F : Set Θ := {θ' | law θ' = law θ₀}
  set K : Set Θ := {θ | ε ≤ infDist θ F}
  have hK : IsCompact K := (isClosed_le continuous_const (continuous_infDist_pt F)).isCompact
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, one_pos, fun θ hθ => ?_⟩
    exact absurd (show θ ∈ K from hθ) (hK0 ▸ Set.notMem_empty θ)
  obtain ⟨θ₁, hθ₁K, hθ₁⟩ := hK.exists_isMinOn hKne
    (hlaw.dist continuous_const).continuousOn (f := fun θ => dist (law θ) (law θ₀))
  refine ⟨dist (law θ₁) (law θ₀), dist_pos.2 fun h => ?_, fun θ hθ => hθ₁ hθ⟩
  have h0 : infDist θ₁ F = 0 := infDist_zero_of_mem (show law θ₁ = law θ₀ from h)
  exact absurd (show ε ≤ infDist θ₁ F from hθ₁K) (by rw [h0]; exact not_le.2 hε)

end Separation

/-! ## Consistency from convergent frequencies -/

section Consistency

variable [MetricSpace Θ] [CompactSpace Θ] [Fintype σ] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω}

omit [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Ω] in
/-- A minimum-distance estimate is at most twice as far (in law) from the truth as the
frequency estimate: `dist (law (est n ω)) (law θ₀) ≤ 2 * dist (freq n ω) (law θ₀)`. -/
theorem dist_law_le_two_mul {law : Θ → σ → ℝ} {freq : ℕ → Ω → σ → ℝ} {est : ℕ → Ω → Θ}
    (hest : IsMinDistEstimator law freq est) (θ₀ : Θ) (n : ℕ) (ω : Ω) :
    dist (law (est n ω)) (law θ₀) ≤ 2 * dist (freq n ω) (law θ₀) := by
  have h := hest n ω θ₀
  calc dist (law (est n ω)) (law θ₀)
      ≤ dist (law (est n ω)) (freq n ω) + dist (freq n ω) (law θ₀) := dist_triangle _ _ _
    _ ≤ dist (law θ₀) (freq n ω) + dist (freq n ω) (law θ₀) := by gcongr
    _ = 2 * dist (freq n ω) (law θ₀) := by rw [dist_comm (law θ₀)]; ring

/-- **Consistency to the fibre** (no identifiability): if the frequency estimates converge in
probability to `law θ₀`, a minimum-distance estimator converges in probability to the fibre
`{θ | law θ = law θ₀}` of parameters with the same law. -/
theorem tendstoInMeasure_infDist_fiber {law : Θ → σ → ℝ} (hlaw : Continuous law) {θ₀ : Θ}
    {freq : ℕ → Ω → σ → ℝ} {est : ℕ → Ω → Θ} (hest : IsMinDistEstimator law freq est)
    (hfreq : TendstoInMeasure P freq atTop fun _ => law θ₀) :
    TendstoInMeasure P (fun n ω => infDist (est n ω) {θ | law θ = law θ₀}) atTop
      fun _ => 0 := by
  rw [tendstoInMeasure_iff_dist] at hfreq ⊢
  intro ε hε
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_dist_law hlaw θ₀ hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hfreq (δ / 2)
    (half_pos hδ)) (fun _ => bot_le) fun n => measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg infDist_nonneg] at hω ⊢
  linarith [hsep _ hω, dist_law_le_two_mul hest θ₀ n ω]

/-- **Consistency up to the permitted symmetries, from convergent frequencies**: if `law`
identifies `θ₀` up to the class `E` (`law θ = law θ₀ → θ ∈ E`) and the frequency estimates
converge in probability to `law θ₀`, then `infDist (est n) E → 0` in probability. -/
theorem tendstoInMeasure_infDist_of_tendstoInMeasure {law : Θ → σ → ℝ} (hlaw : Continuous law)
    {θ₀ : Θ} {E : Set Θ} (hId : ∀ θ, law θ = law θ₀ → θ ∈ E) {freq : ℕ → Ω → σ → ℝ}
    {est : ℕ → Ω → Θ} (hest : IsMinDistEstimator law freq est)
    (hfreq : TendstoInMeasure P freq atTop fun _ => law θ₀) :
    TendstoInMeasure P (fun n ω => infDist (est n ω) E) atTop fun _ => 0 := by
  have hF := tendstoInMeasure_infDist_fiber hlaw hest hfreq
  rw [tendstoInMeasure_iff_dist] at hF ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hF ε hε)
    (fun _ => bot_le) fun n => measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg infDist_nonneg] at hω ⊢
  exact hω.trans (infDist_le_infDist_of_subset hId ⟨θ₀, rfl⟩)

end Consistency

/-! ## The sampling law -/

section Sampling

variable [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [MeasurableSpace σ] [MeasurableSingletonClass σ] [MeasurableSpace Ω] in
/-- The count of columns showing pattern `a` is a sum of indicators. -/
private lemma empiricalFreq_apply (X : ℕ → Ω → σ) (n : ℕ) (ω : Ω) (a : σ) :
    empiricalFreq X n ω a =
      (∑ i ∈ range n, ({a} : Set σ).indicator (1 : σ → ℝ) (X i ω)) / n := by
  rw [empiricalFreq, natCast_card_filter, div_eq_inv_mul]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  simp [Set.indicator_apply]

/-- The empirical frequencies are measurable when the columns are. -/
theorem measurable_empiricalFreq {X : ℕ → Ω → σ} (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (empiricalFreq X n) := by
  refine Measurable.of_eval fun a => ?_
  simp_rw [empiricalFreq_apply]
  refine Measurable.div_const (Finset.measurable_sum _ fun i _ => ?_) _
  exact (measurable_const.indicator (measurableSet_singleton a)).comp (hX i)

/-- **Sampling law ⇒ convergence of the empirical frequencies (almost surely)**: if the columns
`X i` are measurable, pairwise independent and identically distributed with
`P (X 0 = a) = q a`, then `empiricalFreq X n ω → q` for almost every `ω` (strong law of large
numbers, applied to each pattern indicator). -/
theorem ae_tendsto_empiricalFreq [Finite σ] [IsFiniteMeasure P] {X : ℕ → Ω → σ}
    (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {q : σ → ℝ} (hq : ∀ a, P.real (X 0 ⁻¹' {a}) = q a) :
    ∀ᵐ ω ∂P, Tendsto (fun n => empiricalFreq X n ω) atTop (𝓝 q) := by
  have key : ∀ a, ∀ᵐ ω ∂P, Tendsto (fun n => empiricalFreq X n ω a) atTop (𝓝 (q a)) := by
    intro a
    set g : σ → ℝ := ({a} : Set σ).indicator 1 with hg_def
    have hg : Measurable g := measurable_const.indicator (measurableSet_singleton a)
    set Y : ℕ → Ω → ℝ := fun i ω => g (X i ω) with hY
    have hYint : Integrable (Y 0) P := by
      refine (integrable_const (1 : ℝ)).mono' (hg.comp (hX 0)).aestronglyMeasurable ?_
      filter_upwards with ω
      by_cases h : X 0 ω = a <;> simp [hY, hg_def, h]
    have hpair : Pairwise ((· ⟂ᵢ[P] ·) on Y) := fun i j hij => (hindep hij).comp hg hg
    have hident' : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i => (hident i).comp hg
    have hmean : P[Y 0] = q a := by
      have : Y 0 = (X 0 ⁻¹' {a}).indicator 1 := by
        ext ω; by_cases h : X 0 ω = a <;> simp [hY, hg_def, h]
      rw [this, integral_indicator_one (hX 0 (measurableSet_singleton a)), hq]
    have H := strong_law_ae_real Y hYint hpair hident'
    rw [hmean] at H
    filter_upwards [H] with ω hω
    exact hω.congr fun n => (empiricalFreq_apply X n ω a).symm
  filter_upwards [ae_all_iff.2 key] with ω hω
  exact tendsto_pi_nhds.2 hω

/-- **Sampling law ⇒ convergence of the empirical frequencies in probability.** -/
theorem tendstoInMeasure_empiricalFreq [Fintype σ] [IsFiniteMeasure P] {X : ℕ → Ω → σ}
    (hX : ∀ i, Measurable (X i)) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {q : σ → ℝ}
    (hq : ∀ a, P.real (X 0 ⁻¹' {a}) = q a) :
    TendstoInMeasure P (empiricalFreq X) atTop fun _ => q :=
  tendstoInMeasure_of_tendsto_ae (fun n => (measurable_empiricalFreq hX n).aestronglyMeasurable)
    (ae_tendsto_empiricalFreq hX hindep hident hq)

end Sampling

/-! ## The GTR inference corollary -/

section Corollary

variable [MetricSpace Θ] [CompactSpace Θ] [Fintype σ] [DecidableEq σ] [MeasurableSpace σ]
  [MeasurableSingletonClass σ] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsFiniteMeasure P]

/-- **GTR inference corollary** (identifiability + sampling law ⇒ consistency). Let `Θ` be a
compact parameter space with a continuous site-pattern law `law`, and let the true parameter
`θ₀` be identified up to the class `E` of symmetry-equivalent parameters
(`hId : law θ = law θ₀ → θ ∈ E`, the T66 identifiability input). If the alignment columns are
pairwise independent and identically distributed with `P (X 0 = a) = law θ₀ a`, then every
minimum-distance estimator `est` for the empirical site-pattern frequencies satisfies
`infDist (est n) E → 0` in probability. -/
theorem tendstoInMeasure_infDist_minDist {law : Θ → σ → ℝ} (hlaw : Continuous law) {θ₀ : Θ}
    {E : Set Θ} (hId : ∀ θ, law θ = law θ₀ → θ ∈ E) {X : ℕ → Ω → σ}
    (hX : ∀ i, Measurable (X i)) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = law θ₀ a)
    {est : ℕ → Ω → Θ} (hest : IsMinDistEstimator law (empiricalFreq X) est) :
    TendstoInMeasure P (fun n ω => infDist (est n ω) E) atTop fun _ => 0 :=
  tendstoInMeasure_infDist_of_tendstoInMeasure hlaw hId hest
    (tendstoInMeasure_empiricalFreq hX hindep hident hsample)

/-- The GTR inference corollary for the chosen estimator `minDistEstimator`. -/
theorem tendstoInMeasure_infDist_minDistEstimator [Nonempty Θ] {law : Θ → σ → ℝ}
    (hlaw : Continuous law) {θ₀ : Θ} {E : Set Θ} (hId : ∀ θ, law θ = law θ₀ → θ ∈ E)
    {X : ℕ → Ω → σ} (hX : ∀ i, Measurable (X i)) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = law θ₀ a) :
    TendstoInMeasure P (fun n ω => infDist (minDistEstimator hlaw (empiricalFreq X) n ω) E)
      atTop fun _ => 0 :=
  tendstoInMeasure_infDist_minDist hlaw hId hX hindep hident hsample
    (isMinDistEstimator_minDistEstimator hlaw _)

/-- **Full identifiability**: if `law` is injective at `θ₀` (`E = {θ₀}`), every minimum-distance
estimator converges to `θ₀` in probability. -/
theorem tendstoInMeasure_minDist_of_injective {law : Θ → σ → ℝ} (hlaw : Continuous law)
    {θ₀ : Θ} (hId : ∀ θ, law θ = law θ₀ → θ = θ₀) {X : ℕ → Ω → σ}
    (hX : ∀ i, Measurable (X i)) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = law θ₀ a)
    {est : ℕ → Ω → Θ} (hest : IsMinDistEstimator law (empiricalFreq X) est) :
    TendstoInMeasure P est atTop fun _ => θ₀ := by
  have h := tendstoInMeasure_infDist_minDist hlaw (E := {θ₀}) hId hX hindep hident hsample hest
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  simpa [infDist_singleton] using h ε hε

end Corollary

end MathlibExt.Biology.Phylogenetics.GTRInference
