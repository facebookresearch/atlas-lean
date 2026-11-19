/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.StrongLaw
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Wald consistency of the maximum-likelihood estimator

This file proves that the **maximum-likelihood estimator over a compact parameter set converges
almost surely to the true parameter**, under the three primitive conditions of Wald's argument:
compactness of the parameter set, a uniform law of large numbers for the average
log-likelihood, and identifiability (the population criterion has a unique maximizer at the
truth). The parameter is a point of an arbitrary pseudometric space, so the vector case
(`Θ = ℝᵈ`, or any finite-dimensional normed space, with a closed bounded parameter set) is the
special case `ae_tendsto_of_isMLEOn_of_isClosed_of_isBounded`.

`EstimatedInformation` and `MLEAsymptoticNormality` take a consistent root `θhat n → θ₀` as an
input; `tendstoInMeasure_of_isMLEOn` supplies it, in the form `TendstoInMeasure P θhat atTop
fun _ => θ₀` used there, for any (a.e. strongly measurable) maximum-likelihood estimator.

## Setting (source-frozen)

* `ℓ : Θ → α → ℝ` is the log-likelihood of one observation, `ℓ θ x = log p_θ(x)`; no density
  structure is used, only the criterion. `X : ℕ → Ω → α` is the sample.
* The **average log-likelihood** of the first `n` observations is
  `avgLogLik ℓ X n ω θ = n⁻¹ * ∑ i < n, ℓ θ (X i ω)` and the **population criterion** is
  `popCrit P ℓ X θ = ∫ ℓ θ (X 0) dP`, the expected log-likelihood under the true law.
* `est` is a **maximum-likelihood estimator on `K`** (`IsMLEOn`): `est n ω ∈ K` maximizes
  `avgLogLik ℓ X n ω` over `K`. It need not be measurable for the almost-sure statement.
* **Compactness**: `K` is compact.
* **Uniform LLN** (`UniformLLNOn`): almost surely, `avgLogLik ℓ X n ω → popCrit P ℓ X` uniformly
  on `K`. It is a hypothesis of the main theorems and is *derived* for log-likelihoods of finite
  rank, `ℓ θ x = ∑ j < m, a j θ * g j x` with `a j` bounded on `K` and `g j (X 0)` integrable
  (an exponential family with natural parameter continuous on `K` and integrable sufficient
  statistic and log base density, e.g. Bernoulli, Poisson and Gaussian models), from the strong
  law for pairwise independent identically distributed data (`uniformLLNOn_of_finiteRank`).
* **Identifiability** (`IsIdentifiedOn`): `θ₀ ∈ K` and `popCrit P ℓ X θ < popCrit P ℓ X θ₀` for
  every `θ ∈ K` with `θ ≠ θ₀`. For a correctly specified model this is the information
  inequality together with identifiability of the law, derived in
  `InformationInequalityIdentification`.
* **Regularity**: either the population criterion is upper semicontinuous on `K` (Wald's
  condition), or `θ ↦ ℓ θ x` is continuous on `K` for every `x`, in which case the population
  criterion is continuous on `K` as a uniform limit of continuous functions and no condition on
  it is needed.

The argument is the argmax form of Wald's proof (Newey–McFadden, Theorem 2.1; van der Vaart,
Theorem 5.7): an identified maximum of an upper semicontinuous criterion on a compact set is
well separated (`exists_pos_add_le_of_isIdentifiedOn`), and near-maximizers of uniformly close
criteria are then close to `θ₀` (`tendsto_of_tendstoUniformlyOn_of_le_add`).

## Main definitions

* `avgLogLik`, `popCrit`: the average log-likelihood and the population criterion.
* `IsMLEOn`: `est` maximizes the average log-likelihood over `K`.
* `IsIdentifiedOn`: the criterion has a unique maximizer on `K` at `θ₀`.
* `UniformLLNOn`: the almost-sure uniform law of large numbers on `K`.

## Main results

* `exists_pos_add_le_of_isIdentifiedOn`: an identified maximum is well separated.
* `tendsto_of_tendstoUniformlyOn_of_le_add`: **Wald's argmax theorem** (deterministic core),
  for near-maximizers; `tendsto_of_tendstoUniformlyOn` for exact maximizers.
* `ae_tendsto_of_isMLEOn_of_upperSemicontinuousOn`: **almost-sure consistency** of the MLE
  under compactness, uniform LLN, identifiability and an upper semicontinuous criterion.
* `ae_tendsto_of_isMLEOn`: the same with `θ ↦ ℓ θ x` continuous on `K` instead.
* `ae_eventually_mem_of_isMLEOn`: Wald's formulation, the MLE eventually lies in every
  neighbourhood of `θ₀`, almost surely.
* `ae_tendsto_of_isMLEOn_of_isClosed_of_isBounded`: the vector case, `K` closed and bounded in
  a proper space such as `ℝᵈ`.
* `tendstoInMeasure_of_isMLEOn`: consistency in probability, the input of
  `EstimatedInformation`.
* `exists_isMLEOn`: an MLE exists when `K` is compact and nonempty and `θ ↦ ℓ θ x` is
  continuous on `K`.
* `uniformLLNOn_of_finiteRank`, `uniformLLNOn_of_finiteRank_of_continuousOn`: the uniform LLN
  for finite-rank log-likelihoods of pairwise independent identically distributed data.

## Scope

Wald's original theorem replaces the uniform LLN by an integrable upper envelope and a finite
cover; that form, unbounded parameter sets (which need a separate argument that the MLE stays
in a compact set), rates and asymptotic normality are outside this file. The uniform LLN is a
hypothesis of the main theorems and is derived here only for finite-rank log-likelihoods
`ℓ θ x = ∑ j, a j θ * g j x` (`uniformLLNOn_of_finiteRank`). Identifiability is the
unique-maximizer condition `IsIdentifiedOn` on the population criterion; its derivation from
identifiability of the law via the information inequality is in
`InformationInequalityIdentification`.

## References

* A. Wald, *Note on the consistency of the maximum likelihood estimate*, Annals of Mathematical
  Statistics 20 (1949), 595–601.
* W. K. Newey and D. McFadden, *Large sample estimation and hypothesis testing*, Handbook of
  Econometrics, vol. 4, ch. 36, Elsevier, 1994, pp. 2111–2245; Theorem 2.1 (p. 2121).
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998; Theorem 5.7
  (p. 45).
-/

@[expose] public section

open Filter Finset Function MeasureTheory ProbabilityTheory Metric Topology

namespace MathlibExt.Probability.Statistics.MLEConsistency

variable {Θ α Ω : Type*}

/-! ## The maximum-likelihood setup -/

section Setup

/-- The **average log-likelihood** of the first `n` observations of the sample `X` at `θ`:
`n⁻¹ * ∑ i < n, ℓ θ (X i ω)`. -/
noncomputable def avgLogLik (ℓ : Θ → α → ℝ) (X : ℕ → Ω → α) (n : ℕ) (ω : Ω) (θ : Θ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ range n, ℓ θ (X i ω)

/-- `est` is a **maximum-likelihood estimator on `K`**: for every `n` and `ω`, `est n ω ∈ K`
maximizes the average log-likelihood `avgLogLik ℓ X n ω` over `K`. -/
def IsMLEOn (K : Set Θ) (ℓ : Θ → α → ℝ) (X : ℕ → Ω → α) (est : ℕ → Ω → Θ) : Prop :=
  ∀ n ω, est n ω ∈ K ∧ ∀ θ ∈ K, avgLogLik ℓ X n ω θ ≤ avgLogLik ℓ X n ω (est n ω)

/-- **Identifiability on `K`**: `θ₀ ∈ K` is the unique maximizer of `Q` on `K`. -/
def IsIdentifiedOn (K : Set Θ) (Q : Θ → ℝ) (θ₀ : Θ) : Prop :=
  θ₀ ∈ K ∧ ∀ θ ∈ K, θ ≠ θ₀ → Q θ < Q θ₀

variable [MeasurableSpace Ω]

/-- The **population criterion**: the expected log-likelihood `∫ ℓ θ (X 0) dP` of one
observation under the true law. -/
noncomputable def popCrit (P : Measure Ω) (ℓ : Θ → α → ℝ) (X : ℕ → Ω → α) (θ : Θ) : ℝ :=
  ∫ ω, ℓ θ (X 0 ω) ∂P

/-- The **uniform law of large numbers on `K`**: for almost every `ω`, the average
log-likelihood converges to the population criterion uniformly on `K`. -/
def UniformLLNOn (P : Measure Ω) (K : Set Θ) (ℓ : Θ → α → ℝ) (X : ℕ → Ω → α) : Prop :=
  ∀ᵐ ω ∂P, TendstoUniformlyOn (fun n θ => avgLogLik ℓ X n ω θ) (popCrit P ℓ X) atTop K

end Setup

/-! ## Wald's argmax theorem -/

section Wald

variable [PseudoMetricSpace Θ]

/-- **An identified maximum is well separated**: if `K` is compact, `Q` is upper semicontinuous
on `K` and `θ₀` is its unique maximizer on `K`, then for every `ε > 0` there is `δ > 0` with
`Q θ + δ ≤ Q θ₀` for every `θ ∈ K` at distance at least `ε` from `θ₀`. -/
theorem exists_pos_add_le_of_isIdentifiedOn {K : Set Θ} (hK : IsCompact K) {Q : Θ → ℝ}
    (hQ : UpperSemicontinuousOn Q K) {θ₀ : Θ} (hId : IsIdentifiedOn K Q θ₀) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ θ ∈ K, ε ≤ dist θ θ₀ → Q θ + δ ≤ Q θ₀ := by
  set S : Set Θ := K ∩ {θ | ε ≤ dist θ θ₀}
  have hS : IsCompact S :=
    hK.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · refine ⟨1, one_pos, fun θ hθK hθ => ?_⟩
    exact absurd (show θ ∈ S from ⟨hθK, hθ⟩) (hS0 ▸ Set.notMem_empty θ)
  obtain ⟨θ₁, hθ₁S, hθ₁⟩ := (hQ.mono Set.inter_subset_left).exists_isMaxOn hSne hS
  have hne : θ₁ ≠ θ₀ := fun h => by
    have h1 : ε ≤ dist θ₁ θ₀ := hθ₁S.2
    rw [h, dist_self] at h1
    linarith
  have hlt := hId.2 θ₁ hθ₁S.1 hne
  exact ⟨Q θ₀ - Q θ₁, sub_pos.2 hlt, fun θ hθK hθ => by
    linarith [isMaxOn_iff.1 hθ₁ θ ⟨hθK, hθ⟩]⟩

/-- **One step of Wald's argument**: if the maximum of `Q` on `K` is separated by `δ` outside the
`ε`-ball around `θ₀`, the criterion `Qn` is within `δ / 3` of `Q` on `K`, and `θh ∈ K` does at
least as well as `θ₀` for `Qn` up to `η < δ / 3`, then `θh` lies in the `ε`-ball. -/
theorem dist_lt_of_forall_abs_sub_lt {K : Set Θ} {Q Qn : Θ → ℝ} {θ₀ θh : Θ} {ε δ η : ℝ}
    (hsep : ∀ θ ∈ K, ε ≤ dist θ θ₀ → Q θ + δ ≤ Q θ₀) (hθ₀ : θ₀ ∈ K) (hθh : θh ∈ K)
    (hunif : ∀ θ ∈ K, |Qn θ - Q θ| < δ / 3) (hη : η < δ / 3) (hmax : Qn θ₀ ≤ Qn θh + η) :
    dist θh θ₀ < ε := by
  by_contra h
  have h1 := hsep θh hθh (not_lt.1 h)
  have h2 := (abs_lt.1 (hunif θh hθh)).2
  have h3 := (abs_lt.1 (hunif θ₀ hθ₀)).1
  linarith

/-- **Wald's argmax theorem for near-maximizers** (Newey–McFadden, Theorem 2.1; van der Vaart,
Theorem 5.7, deterministic core). Let `K` be compact, `Q` upper semicontinuous on `K` with unique
maximizer `θ₀ ∈ K`, and `Qn n → Q` uniformly on `K`. If `est n ∈ K` and
`Qn n θ₀ ≤ Qn n (est n) + η n` with `η n → 0`, then `est n → θ₀`. -/
theorem tendsto_of_tendstoUniformlyOn_of_le_add {K : Set Θ} (hK : IsCompact K) {Q : Θ → ℝ}
    (hQ : UpperSemicontinuousOn Q K) {θ₀ : Θ} (hId : IsIdentifiedOn K Q θ₀)
    {Qn : ℕ → Θ → ℝ} (hunif : TendstoUniformlyOn Qn Q atTop K) {est : ℕ → Θ}
    (hestK : ∀ n, est n ∈ K) {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hmax : ∀ n, Qn n θ₀ ≤ Qn n (est n) + η n) : Tendsto est atTop (𝓝 θ₀) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_add_le_of_isIdentifiedOn hK hQ hId hε
  have hδ3 : 0 < δ / 3 := by positivity
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hunif (δ / 3) hδ3)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hη.eventually (gt_mem_nhds hδ3))
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  refine dist_lt_of_forall_abs_sub_lt hsep hId.1 (hestK n) (fun θ hθ => ?_)
    (hN₂ n (le_of_max_le_right hn)) (hmax n)
  rw [abs_sub_comm, ← Real.dist_eq]
  exact hN₁ n (le_of_max_le_left hn) θ hθ

/-- **Wald's argmax theorem** for exact maximizers: under the hypotheses of
`tendsto_of_tendstoUniformlyOn_of_le_add`, maximizers `est n ∈ K` of `Qn n` on `K` converge to
`θ₀`. -/
theorem tendsto_of_tendstoUniformlyOn {K : Set Θ} (hK : IsCompact K) {Q : Θ → ℝ}
    (hQ : UpperSemicontinuousOn Q K) {θ₀ : Θ} (hId : IsIdentifiedOn K Q θ₀)
    {Qn : ℕ → Θ → ℝ} (hunif : TendstoUniformlyOn Qn Q atTop K) {est : ℕ → Θ}
    (hestK : ∀ n, est n ∈ K) (hmax : ∀ n, Qn n θ₀ ≤ Qn n (est n)) :
    Tendsto est atTop (𝓝 θ₀) :=
  tendsto_of_tendstoUniformlyOn_of_le_add hK hQ hId hunif hestK tendsto_const_nhds
    fun n => by simpa using hmax n

end Wald

/-! ## Continuity and existence -/

section Existence

variable [TopologicalSpace Θ]

/-- If `θ ↦ ℓ θ x` is continuous on `K` for every `x`, so is the average log-likelihood. -/
theorem continuousOn_avgLogLik {K : Set Θ} {ℓ : Θ → α → ℝ}
    (hcont : ∀ x, ContinuousOn (fun θ => ℓ θ x) K) (X : ℕ → Ω → α) (n : ℕ) (ω : Ω) :
    ContinuousOn (avgLogLik ℓ X n ω) K :=
  continuousOn_const.mul (continuousOn_finsetSum _ fun i _ => hcont (X i ω))

/-- **Existence of the MLE**: on a nonempty compact `K`, with `θ ↦ ℓ θ x` continuous on `K`,
the average log-likelihood attains its maximum, so a maximum-likelihood estimator exists. -/
theorem exists_isMLEOn {K : Set Θ} (hK : IsCompact K) (hne : K.Nonempty) {ℓ : Θ → α → ℝ}
    (hcont : ∀ x, ContinuousOn (fun θ => ℓ θ x) K) (X : ℕ → Ω → α) :
    ∃ est : ℕ → Ω → Θ, IsMLEOn K ℓ X est := by
  have h : ∀ n ω, ∃ θ ∈ K, IsMaxOn (avgLogLik ℓ X n ω) K θ := fun n ω =>
    hK.exists_isMaxOn hne (continuousOn_avgLogLik hcont X n ω)
  choose est hestK hmax using h
  exact ⟨est, fun n ω => ⟨hestK n ω, fun θ hθ => isMaxOn_iff.1 (hmax n ω) θ hθ⟩⟩

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- Along a sample path on which the uniform LLN holds, the population criterion is continuous on
`K` when `θ ↦ ℓ θ x` is: it is a uniform limit of continuous functions. -/
theorem continuousOn_popCrit_of_tendstoUniformlyOn {K : Set Θ} {ℓ : Θ → α → ℝ}
    (hcont : ∀ x, ContinuousOn (fun θ => ℓ θ x) K) {X : ℕ → Ω → α} {ω : Ω}
    (hω : TendstoUniformlyOn (fun n θ => avgLogLik ℓ X n ω θ) (popCrit P ℓ X) atTop K) :
    ContinuousOn (popCrit P ℓ X) K :=
  hω.continuousOn (Frequently.of_forall fun n => continuousOn_avgLogLik hcont X n ω)

end Existence

/-! ## Almost-sure consistency -/

section Consistency

variable [PseudoMetricSpace Θ] [MeasurableSpace Ω] {P : Measure Ω}

/-- **Wald consistency of the MLE, almost surely** (upper semicontinuous criterion). Let `K` be
compact, the population criterion upper semicontinuous on `K` with unique maximizer `θ₀ ∈ K`
(identifiability), and the uniform LLN hold on `K`. Then every maximum-likelihood estimator on
`K` converges to `θ₀` almost surely. -/
theorem ae_tendsto_of_isMLEOn_of_upperSemicontinuousOn {K : Set Θ} (hK : IsCompact K)
    {ℓ : Θ → α → ℝ} {X : ℕ → Ω → α} (hQ : UpperSemicontinuousOn (popCrit P ℓ X) K) {θ₀ : Θ}
    (hId : IsIdentifiedOn K (popCrit P ℓ X) θ₀) (hULLN : UniformLLNOn P K ℓ X)
    {est : ℕ → Ω → Θ} (hest : IsMLEOn K ℓ X est) :
    ∀ᵐ ω ∂P, Tendsto (fun n => est n ω) atTop (𝓝 θ₀) := by
  filter_upwards [hULLN] with ω hω
  exact tendsto_of_tendstoUniformlyOn hK hQ hId hω (fun n => (hest n ω).1)
    fun n => (hest n ω).2 θ₀ hId.1

/-- **Wald consistency of the MLE, almost surely** (continuous log-likelihood). Let `K` be
compact, `θ ↦ ℓ θ x` continuous on `K` for every `x`, the uniform LLN hold on `K`, and the
population criterion have the unique maximizer `θ₀ ∈ K`. Then every maximum-likelihood estimator
on `K` converges to `θ₀` almost surely. No regularity of the population criterion is assumed: it
is continuous on `K` as a uniform limit. -/
theorem ae_tendsto_of_isMLEOn {K : Set Θ} (hK : IsCompact K) {ℓ : Θ → α → ℝ}
    (hcont : ∀ x, ContinuousOn (fun θ => ℓ θ x) K) {X : ℕ → Ω → α} {θ₀ : Θ}
    (hId : IsIdentifiedOn K (popCrit P ℓ X) θ₀) (hULLN : UniformLLNOn P K ℓ X)
    {est : ℕ → Ω → Θ} (hest : IsMLEOn K ℓ X est) :
    ∀ᵐ ω ∂P, Tendsto (fun n => est n ω) atTop (𝓝 θ₀) := by
  filter_upwards [hULLN] with ω hω
  have hQ := (continuousOn_popCrit_of_tendstoUniformlyOn hcont hω).upperSemicontinuousOn
  exact tendsto_of_tendstoUniformlyOn hK hQ hId hω (fun n => (hest n ω).1)
    fun n => (hest n ω).2 θ₀ hId.1

/-- **Wald's formulation**: under the hypotheses of `ae_tendsto_of_isMLEOn`, almost surely the
MLE eventually lies in every neighbourhood of `θ₀`. -/
theorem ae_eventually_mem_of_isMLEOn {K : Set Θ} (hK : IsCompact K) {ℓ : Θ → α → ℝ}
    (hcont : ∀ x, ContinuousOn (fun θ => ℓ θ x) K) {X : ℕ → Ω → α} {θ₀ : Θ}
    (hId : IsIdentifiedOn K (popCrit P ℓ X) θ₀) (hULLN : UniformLLNOn P K ℓ X)
    {est : ℕ → Ω → Θ} (hest : IsMLEOn K ℓ X est) :
    ∀ᵐ ω ∂P, ∀ U ∈ 𝓝 θ₀, ∀ᶠ n in atTop, est n ω ∈ U := by
  filter_upwards [ae_tendsto_of_isMLEOn hK hcont hId hULLN hest] with ω hω U hU using hω hU

/-- **The vector MLE**: in a proper space such as `ℝᵈ`, a closed bounded parameter set is
compact, so under continuity, the uniform LLN and identifiability every MLE on `K` converges to
`θ₀` almost surely. -/
theorem ae_tendsto_of_isMLEOn_of_isClosed_of_isBounded [ProperSpace Θ] {K : Set Θ}
    (hKc : IsClosed K) (hKb : Bornology.IsBounded K) {ℓ : Θ → α → ℝ}
    (hcont : ∀ x, ContinuousOn (fun θ => ℓ θ x) K) {X : ℕ → Ω → α} {θ₀ : Θ}
    (hId : IsIdentifiedOn K (popCrit P ℓ X) θ₀) (hULLN : UniformLLNOn P K ℓ X)
    {est : ℕ → Ω → Θ} (hest : IsMLEOn K ℓ X est) :
    ∀ᵐ ω ∂P, Tendsto (fun n => est n ω) atTop (𝓝 θ₀) :=
  ae_tendsto_of_isMLEOn (Metric.isCompact_of_isClosed_isBounded hKc hKb) hcont hId hULLN hest

/-- **Consistency in probability**, the consistent-root input of `EstimatedInformation`: under
the hypotheses of `ae_tendsto_of_isMLEOn`, a finite measure and an a.e. strongly measurable MLE,
`est n → θ₀` in probability. -/
theorem tendstoInMeasure_of_isMLEOn [IsFiniteMeasure P] {K : Set Θ} (hK : IsCompact K)
    {ℓ : Θ → α → ℝ} (hcont : ∀ x, ContinuousOn (fun θ => ℓ θ x) K) {X : ℕ → Ω → α} {θ₀ : Θ}
    (hId : IsIdentifiedOn K (popCrit P ℓ X) θ₀) (hULLN : UniformLLNOn P K ℓ X)
    {est : ℕ → Ω → Θ} (hest : IsMLEOn K ℓ X est)
    (hmeas : ∀ n, AEStronglyMeasurable (est n) P) :
    TendstoInMeasure P est atTop fun _ => θ₀ :=
  tendstoInMeasure_of_tendsto_ae hmeas (ae_tendsto_of_isMLEOn hK hcont hId hULLN hest)

end Consistency

/-! ## The uniform law of large numbers for finite-rank log-likelihoods -/

section FiniteRank

/-- The average log-likelihood of a finite-rank log-likelihood `ℓ θ x = ∑ j, a j θ * g j x` is
`∑ j, a j θ * (n⁻¹ * ∑ i < n, g j (X i ω))`. -/
theorem avgLogLik_eq_sum_of_finiteRank {ℓ : Θ → α → ℝ} {m : ℕ} (a : Fin m → Θ → ℝ)
    (g : Fin m → α → ℝ) (hℓ : ∀ θ x, ℓ θ x = ∑ j, a j θ * g j x) (X : ℕ → Ω → α) (n : ℕ)
    (ω : Ω) (θ : Θ) :
    avgLogLik ℓ X n ω θ = ∑ j, a j θ * ((n : ℝ)⁻¹ * ∑ i ∈ range n, g j (X i ω)) := by
  simp only [avgLogLik, hℓ]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  ring

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- The population criterion of a finite-rank log-likelihood is
`∑ j, a j θ * ∫ g j (X 0) dP`, when every `g j (X 0)` is integrable. -/
theorem popCrit_eq_sum_of_finiteRank {ℓ : Θ → α → ℝ} {m : ℕ} (a : Fin m → Θ → ℝ)
    (g : Fin m → α → ℝ) (hℓ : ∀ θ x, ℓ θ x = ∑ j, a j θ * g j x) {X : ℕ → Ω → α}
    (hint : ∀ j, Integrable (fun ω => g j (X 0 ω)) P) (θ : Θ) :
    popCrit P ℓ X θ = ∑ j, a j θ * ∫ ω, g j (X 0 ω) ∂P := by
  simp only [popCrit, hℓ]
  rw [integral_finsetSum _ fun j _ => (hint j).const_mul (a j θ)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- **Uniform LLN for finite-rank log-likelihoods.** If `ℓ θ x = ∑ j < m, a j θ * g j x` with each
`a j` bounded on `K` and each `g j` measurable with `g j (X 0)` integrable, and the observations
`X i` are pairwise independent and identically distributed, then the uniform LLN holds on `K`.
The proof is the strong law for each of the finitely many statistics `g j (X i)`. -/
theorem uniformLLNOn_of_finiteRank [MeasurableSpace α] {K : Set Θ} {ℓ : Θ → α → ℝ}
    {X : ℕ → Ω → α} {m : ℕ} (a : Fin m → Θ → ℝ) (g : Fin m → α → ℝ)
    (hℓ : ∀ θ x, ℓ θ x = ∑ j, a j θ * g j x) (hbdd : ∀ j, ∃ C, ∀ θ ∈ K, |a j θ| ≤ C)
    (hg : ∀ j, Measurable (g j)) (hint : ∀ j, Integrable (fun ω => g j (X 0 ω)) P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    UniformLLNOn P K ℓ X := by
  have hslln : ∀ j, ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, g j (X i ω))
      atTop (𝓝 (∫ ω, g j (X 0 ω) ∂P)) := by
    intro j
    have := strong_law_ae (fun i ω => g j (X i ω)) (hint j)
      (fun i k hik => (hindep hik).comp (hg j) (hg j)) (fun i => (hident i).comp (hg j))
    simpa only [smul_eq_mul] using this
  choose C hC using hbdd
  filter_upwards [ae_all_iff.2 hslln] with ω hω
  have he : Tendsto (fun n : ℕ => ∑ j, |C j| *
      |(n : ℝ)⁻¹ * ∑ i ∈ range n, g j (X i ω) - ∫ ω, g j (X 0 ω) ∂P|) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun j _ =>
      (((hω j).sub_const (∫ ω, g j (X 0 ω) ∂P)).abs).const_mul |C j|
    simpa using this
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [he.eventually (gt_mem_nhds hε)] with n hn θ hθ
  rw [Real.dist_eq, popCrit_eq_sum_of_finiteRank a g hℓ hint,
    avgLogLik_eq_sum_of_finiteRank a g hℓ, ← Finset.sum_sub_distrib]
  refine lt_of_le_of_lt ((Finset.abs_sum_le_sum_abs _ _).trans ?_) hn
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← mul_sub, abs_mul, abs_sub_comm]
  exact mul_le_mul_of_nonneg_right ((hC j θ hθ).trans (le_abs_self _)) (abs_nonneg _)

/-- **Uniform LLN for finite-rank log-likelihoods with continuous coefficients**: as
`uniformLLNOn_of_finiteRank`, with the coefficients `a j` continuous on the compact set `K`
instead of bounded on it. -/
theorem uniformLLNOn_of_finiteRank_of_continuousOn [TopologicalSpace Θ] [MeasurableSpace α]
    {K : Set Θ} (hK : IsCompact K) {ℓ : Θ → α → ℝ} {X : ℕ → Ω → α} {m : ℕ}
    (a : Fin m → Θ → ℝ) (g : Fin m → α → ℝ) (hℓ : ∀ θ x, ℓ θ x = ∑ j, a j θ * g j x)
    (ha : ∀ j, ContinuousOn (a j) K) (hg : ∀ j, Measurable (g j))
    (hint : ∀ j, Integrable (fun ω => g j (X 0 ω)) P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    UniformLLNOn P K ℓ X :=
  uniformLLNOn_of_finiteRank a g hℓ (fun j => by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (ha j)
    exact ⟨C, fun θ hθ => by simpa [Real.norm_eq_abs] using hC θ hθ⟩) hg hint hindep hident

end FiniteRank

end MathlibExt.Probability.Statistics.MLEConsistency
