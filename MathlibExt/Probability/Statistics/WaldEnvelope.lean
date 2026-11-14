/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MLEConsistency

/-!
# Wald consistency under Wald's original conditions

`MLEConsistency` proves almost-sure consistency of the maximum-likelihood estimator on a compact
parameter set from a uniform law of large numbers. This file proves it under **Wald's original
conditions** (Wald 1949): an integrable upper envelope of the log-likelihood on each set of a
finite cover of the parameter set away from the truth, with no compactness of the parameter set
and no uniform law of large numbers.

## Setting

The objects are those of `MLEConsistency`: the log-likelihood `ℓ : Θ → α → ℝ`, the sample
`X : ℕ → Ω → α`, the average log-likelihood `avgLogLik`, the population criterion `popCrit` and a
maximum-likelihood estimator `est` on the parameter set `S` (`IsMLEOn S ℓ X est`). The
observations are pairwise independent and identically distributed, `ℓ θ₀` is measurable and
`ℓ θ₀ (X 0)` is integrable.

* **Wald cover** (`IsWaldCover`): a finite family of pairs `(B, u)` whose sets `B` cover
  `S \ ball θ₀ ε`, with `u` a measurable upper envelope of `ℓ θ` for `θ ∈ B`, `u (X 0)` integrable
  and `E u (X 0) < E ℓ θ₀ (X 0)`. If such a cover exists for every `ε > 0`, every MLE on `S`
  converges to `θ₀` almost surely (`ae_tendsto_of_isMLEOn_of_isWaldCover`). Nothing is assumed of
  `S`, of the topology of `Θ` beyond the pseudometric, or of the regularity of `ℓ`.
* **Local envelopes** (`HasLocalEnvelope`): at `θ`, a sequence `u n` of measurable functions,
  decreasing in `n`, converging pointwise to `ℓ θ`, with `ℓ θ' ≤ u n` for `θ' ∈ S` at distance
  `< 1 / (n + 1)` from `θ`, and `u 0 (X 0)` integrable. This is Wald's condition on the local
  suprema `x ↦ sup {ℓ θ' x | θ' ∈ S, dist θ' θ < ρ}` (measurable, integrable for small `ρ`, and
  tending to `ℓ θ x` as `ρ → 0` by upper semicontinuity), stated for any dominating sequence.
* **Envelope at infinity** (`HasTailEnvelope`): a sequence `v n` of measurable functions,
  decreasing in `n` and tending to `-∞` pointwise, with `ℓ θ ≤ v n` for `θ ∈ S` at distance
  `> n` from a fixed centre, and `v 0 (X 0)` integrable. This is Wald's condition
  `lim_{|θ| → ∞} f(x, θ) = 0` with `E sup_{|θ| > r} log f(X, θ)⁺ < ∞`, in log form.

Local envelopes on a compact set `K`, strict identification at each `θ ∈ K \ {θ₀}` and one
integrable envelope on `S \ K` with mean below `E ℓ θ₀ (X 0)` produce a Wald cover for every `ε`
(`exists_isWaldCover`): dominated convergence lowers the local envelope means below
`E ℓ θ₀ (X 0)`, and compactness extracts a finite subcover. In a proper space (such as `ℝᵈ`)
with `S` closed, the envelope at infinity supplies the compact core `S ∩ closedBall θc n` and the
envelope on its complement, which gives Wald's 1949 theorem
(`ae_tendsto_of_isMLEOn_of_hasTailEnvelope`).

## Main definitions

* `IsWaldCover`: a finite cover of `S \ ball θ₀ ε` by sets with integrable upper envelopes whose
  means are below the population criterion at `θ₀`.
* `HasLocalEnvelope`: Wald's local upper envelopes at a parameter.
* `HasTailEnvelope`: Wald's upper envelope at infinity.

## Main results

* `eventually_dist_lt_of_isWaldCover`: the deterministic core, along a sample path on which the
  averages of the finitely many envelopes and of `ℓ θ₀` converge to their means, the MLE is
  eventually within `ε` of `θ₀`.
* `ae_tendsto_of_isMLEOn_of_isWaldCover`: **Wald consistency from finite covers**, almost surely,
  with no compactness assumption.
* `exists_isWaldCover`: local envelopes on a compact set plus an envelope off it give the cover.
* `ae_tendsto_of_isMLEOn_of_hasLocalEnvelope`: Wald consistency on a compact parameter set from
  local envelopes alone, with no uniform law of large numbers.
* `ae_tendsto_of_isMLEOn_of_hasTailEnvelope`: **Wald's theorem (1949)**, a closed parameter set in
  a proper space, local envelopes and an envelope at infinity.
* `tendstoInMeasure_of_isMLEOn_of_hasTailEnvelope`: the same, in probability.

## References

* A. Wald, *Note on the consistency of the maximum likelihood estimate*, Annals of Mathematical
  Statistics 20 (1949), 595–601; assumptions 1–8 and Theorems 1–2.
* T. S. Ferguson, *A Course in Large Sample Theory*, Chapman & Hall, 1996; Theorem 17 (p. 114).
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998; Theorem 5.14
  (p. 48).
-/

@[expose] public section

open Filter Finset Function MeasureTheory ProbabilityTheory Metric Topology

namespace MathlibExt.Probability.Statistics.WaldEnvelope

open MathlibExt.Probability.Statistics.MLEConsistency

variable {Θ α Ω : Type*} [PseudoMetricSpace Θ] [MeasurableSpace α] [MeasurableSpace Ω]
  {P : Measure Ω}

/-! ## Definitions -/

section Definitions

/-- A **Wald cover** of `S` away from `θ₀` at radius `ε`: a finite set `C` of pairs `(B, u)` whose
sets `B` cover `S \ ball θ₀ ε`, where each `u` is a measurable upper envelope of `ℓ θ` for every
`θ ∈ B`, `u (X 0)` is integrable, and `E u (X 0)` is strictly below the population criterion at
`θ₀`. -/
def IsWaldCover (P : Measure Ω) (ℓ : Θ → α → ℝ) (X : ℕ → Ω → α) (S : Set Θ) (θ₀ : Θ) (ε : ℝ)
    (C : Set (Set Θ × (α → ℝ))) : Prop :=
  C.Finite ∧ S \ ball θ₀ ε ⊆ ⋃ p ∈ C, p.1 ∧
    ∀ p ∈ C, Measurable p.2 ∧ Integrable (fun ω => p.2 (X 0 ω)) P ∧
      (∀ θ ∈ p.1, ∀ x, ℓ θ x ≤ p.2 x) ∧ ∫ ω, p.2 (X 0 ω) ∂P < popCrit P ℓ X θ₀

/-- **Wald's local upper envelopes** at `θ`: measurable functions `u n`, decreasing in `n` and
converging pointwise to `ℓ θ`, with `ℓ θ' ≤ u n` for every `θ' ∈ S` at distance
`< 1 / (n + 1)` from `θ`, and `u 0 (X 0)` integrable. -/
def HasLocalEnvelope (P : Measure Ω) (S : Set Θ) (ℓ : Θ → α → ℝ) (X : ℕ → Ω → α) (θ : Θ) :
    Prop :=
  ∃ u : ℕ → α → ℝ, (∀ n, Measurable (u n)) ∧ Integrable (fun ω => u 0 (X 0 ω)) P ∧
    (∀ n : ℕ, ∀ θ' ∈ S, dist θ' θ < 1 / ((n : ℝ) + 1) → ∀ x, ℓ θ' x ≤ u n x) ∧
    (∀ x, Antitone fun n => u n x) ∧ ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (ℓ θ x))

/-- **Wald's upper envelope at infinity** around the centre `θc`: measurable functions `v n`,
decreasing in `n` and tending to `-∞` pointwise, with `ℓ θ ≤ v n` for every `θ ∈ S` at distance
`> n` from `θc`, and `v 0 (X 0)` integrable. -/
def HasTailEnvelope (P : Measure Ω) (S : Set Θ) (ℓ : Θ → α → ℝ) (X : ℕ → Ω → α) (θc : Θ) :
    Prop :=
  ∃ v : ℕ → α → ℝ, (∀ n, Measurable (v n)) ∧ Integrable (fun ω => v 0 (X 0 ω)) P ∧
    (∀ n : ℕ, ∀ θ ∈ S, (n : ℝ) < dist θ θc → ∀ x, ℓ θ x ≤ v n x) ∧
    (∀ x, Antitone fun n => v n x) ∧ ∀ x, Tendsto (fun n => v n x) atTop atBot

end Definitions

/-! ## The deterministic core -/

section Core

omit [PseudoMetricSpace Θ] [MeasurableSpace α] [MeasurableSpace Ω] in
/-- An upper envelope of `ℓ θ` bounds the average log-likelihood at `θ` by the sample average of
the envelope. -/
theorem avgLogLik_le_of_le {ℓ : Θ → α → ℝ} {θ : Θ} {u : α → ℝ} (h : ∀ x, ℓ θ x ≤ u x)
    (X : ℕ → Ω → α) (n : ℕ) (ω : Ω) :
    avgLogLik ℓ X n ω θ ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, u (X i ω) :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h (X i ω))
    (inv_nonneg.2 (Nat.cast_nonneg n))

/-- **Deterministic core of Wald's argument.** Let `C` be a Wald cover at radius `ε`. Along a
sample path `ω` on which the averages of the envelopes and of `ℓ θ₀` converge to their means, a
sequence `est n ∈ S` doing at least as well as `θ₀` for the average log-likelihood is eventually
within `ε` of `θ₀`. -/
theorem eventually_dist_lt_of_isWaldCover {ℓ : Θ → α → ℝ} {X : ℕ → Ω → α} {S : Set Θ}
    {θ₀ : Θ} {ε : ℝ} {C : Set (Set Θ × (α → ℝ))} (hC : IsWaldCover P ℓ X S θ₀ ε C) {ω : Ω}
    (hconv : ∀ p ∈ C, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, p.2 (X i ω)) atTop
      (𝓝 (∫ ω, p.2 (X 0 ω) ∂P)))
    (h₀ : Tendsto (fun n => avgLogLik ℓ X n ω θ₀) atTop (𝓝 (popCrit P ℓ X θ₀)))
    {est : ℕ → Θ} (hestS : ∀ n, est n ∈ S)
    (hmax : ∀ n, avgLogLik ℓ X n ω θ₀ ≤ avgLogLik ℓ X n ω (est n)) :
    ∀ᶠ n in atTop, dist (est n) θ₀ < ε := by
  obtain ⟨hfin, hcov, hprop⟩ := hC
  have hlt : ∀ p ∈ C, ∀ᶠ n : ℕ in atTop,
      (n : ℝ)⁻¹ * ∑ i ∈ range n, p.2 (X i ω) < avgLogLik ℓ X n ω θ₀ := by
    intro p hp
    have h := ((hconv p hp).sub h₀).eventually (gt_mem_nhds (sub_neg.2 (hprop p hp).2.2.2))
    filter_upwards [h] with n hn
    linarith
  filter_upwards [(eventually_all_finite hfin).2 hlt] with n hn
  by_contra hdist
  have hmem : est n ∈ S \ ball θ₀ ε := ⟨hestS n, fun h => hdist (mem_ball.1 h)⟩
  obtain ⟨p, hpC, hpB⟩ := Set.mem_iUnion₂.1 (hcov hmem)
  have h1 := avgLogLik_le_of_le ((hprop p hpC).2.2.1 (est n) hpB) X n ω
  linarith [hn p hpC, hmax n]

end Core

/-! ## Almost-sure consistency from a Wald cover -/

section Cover

/-- The strong law for the sample average of a measurable function of the observations. -/
theorem ae_tendsto_avg {X : ℕ → Ω → α} {g : α → ℝ} (hg : Measurable g)
    (hint : Integrable (fun ω => g (X 0 ω)) P) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, g (X i ω)) atTop
      (𝓝 (∫ ω, g (X 0 ω) ∂P)) := by
  have := strong_law_ae (fun i ω => g (X i ω)) hint
    (fun i k hik => (hindep hik).comp hg hg) (fun i => (hident i).comp hg)
  simpa only [smul_eq_mul] using this

/-- **Wald consistency of the MLE from finite covers**, almost surely. Let the observations be
pairwise independent and identically distributed, `ℓ θ₀` measurable with `ℓ θ₀ (X 0)`
integrable, and suppose that for every `ε > 0` the set `S \ ball θ₀ ε` has a Wald cover: finitely
many sets with integrable upper envelopes of the log-likelihood whose means are below
`E ℓ θ₀ (X 0)`. Then every maximum-likelihood estimator on `S` converges to `θ₀` almost surely.
No compactness of `S` and no uniform law of large numbers is assumed. -/
theorem ae_tendsto_of_isMLEOn_of_isWaldCover {ℓ : Θ → α → ℝ} {X : ℕ → Ω → α} {S : Set Θ}
    {θ₀ : Θ} (hℓ₀ : Measurable (ℓ θ₀)) (hint₀ : Integrable (fun ω => ℓ θ₀ (X 0 ω)) P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hθ₀ : θ₀ ∈ S) (hcover : ∀ ε > 0, ∃ C, IsWaldCover P ℓ X S θ₀ ε C) {est : ℕ → Ω → Θ}
    (hest : IsMLEOn S ℓ X est) :
    ∀ᵐ ω ∂P, Tendsto (fun n => est n ω) atTop (𝓝 θ₀) := by
  have hc : ∀ k : ℕ, ∃ C, IsWaldCover P ℓ X S θ₀ (1 / ((k : ℝ) + 1)) C :=
    fun k => hcover _ Nat.one_div_pos_of_nat
  choose C hC using hc
  have hall : ∀ k, ∀ᵐ ω ∂P, ∀ p ∈ C k, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, p.2 (X i ω)) atTop
      (𝓝 (∫ ω, p.2 (X 0 ω) ∂P)) := fun k =>
    (ae_ball_iff (hC k).1.countable).2 fun p hp =>
      ae_tendsto_avg ((hC k).2.2 p hp).1 ((hC k).2.2 p hp).2.1 hindep hident
  have h₀ : ∀ᵐ ω ∂P, Tendsto (fun n => avgLogLik ℓ X n ω θ₀) atTop
      (𝓝 (popCrit P ℓ X θ₀)) := ae_tendsto_avg hℓ₀ hint₀ hindep hident
  filter_upwards [ae_all_iff.2 hall, h₀] with ω hω hω₀
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_dist_lt_of_isWaldCover (hC k) (hω k) hω₀
    (fun n => (hest n ω).1) fun n => (hest n ω).2 θ₀ hθ₀)
  exact ⟨N, fun n hn => (hN n hn).trans hk⟩

end Cover

/-! ## Wald covers from local envelopes -/

section Local

/-- **Local envelope means converge**: from local envelopes at `θ` with `ℓ θ (X 0)` integrable
and `E ℓ θ (X 0) < E ℓ θ₀ (X 0)`, some ball around `θ` carries a single integrable envelope with
mean below `E ℓ θ₀ (X 0)` (dominated convergence). -/
theorem exists_ball_envelope_lt {S : Set Θ} {ℓ : Θ → α → ℝ} {X : ℕ → Ω → α}
    (hX : AEMeasurable (X 0) P) {θ θ₀ : Θ} (hloc : HasLocalEnvelope P S ℓ X θ)
    (hint : Integrable (fun ω => ℓ θ (X 0 ω)) P) (hlt : popCrit P ℓ X θ < popCrit P ℓ X θ₀) :
    ∃ r > 0, ∃ u : α → ℝ, Measurable u ∧ Integrable (fun ω => u (X 0 ω)) P ∧
      (∀ θ' ∈ S, dist θ' θ < r → ∀ x, ℓ θ' x ≤ u x) ∧ ∫ ω, u (X 0 ω) ∂P < popCrit P ℓ X θ₀ := by
  obtain ⟨u, hmeas, hint0, henv, hanti, hlim⟩ := hloc
  have hlo : ∀ n x, ℓ θ x ≤ u n x := fun n x => (hanti x).le_of_tendsto (hlim x) n
  have hbd : ∀ n x, ‖u n x‖ ≤ |u 0 x| + |ℓ θ x| := fun n x => by
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hlo n x
    have h2 := hanti x (Nat.zero_le n)
    constructor <;> cases abs_cases (u 0 x) <;> cases abs_cases (ℓ θ x) <;> linarith
  have hconv : Tendsto (fun n => ∫ ω, u n (X 0 ω) ∂P) atTop (𝓝 (popCrit P ℓ X θ)) :=
    tendsto_integral_of_dominated_convergence (fun ω => |u 0 (X 0 ω)| + |ℓ θ (X 0 ω)|)
      (fun n => ((hmeas n).comp_aemeasurable hX).aestronglyMeasurable) (hint0.abs.add hint.abs)
      (fun n => ae_of_all _ fun ω => hbd n (X 0 ω)) (ae_of_all _ fun ω => hlim (X 0 ω))
  obtain ⟨n, hn⟩ := (hconv.eventually (gt_mem_nhds hlt)).exists
  refine ⟨1 / ((n : ℝ) + 1), Nat.one_div_pos_of_nat, u n, hmeas n, ?_, henv n, hn⟩
  exact Integrable.mono' (hint0.abs.add hint.abs)
    ((hmeas n).comp_aemeasurable hX).aestronglyMeasurable (ae_of_all _ fun ω => hbd n (X 0 ω))

/-- **Wald covers from local envelopes on a compact set.** Let `K` be compact, and at every
`θ ∈ K` other than `θ₀` let `ℓ θ (X 0)` be integrable with `E ℓ θ (X 0) < E ℓ θ₀ (X 0)` and let
local envelopes exist. If one integrable envelope `uT` of `ℓ θ` for all `θ ∈ S \ K` has mean
below `E ℓ θ₀ (X 0)`, then `S` has a Wald cover at every radius `ε > 0`. -/
theorem exists_isWaldCover {S K : Set Θ} (hK : IsCompact K) {ℓ : Θ → α → ℝ} {X : ℕ → Ω → α}
    (hX : AEMeasurable (X 0) P) {θ₀ : Θ}
    (hint : ∀ θ ∈ K, θ ≠ θ₀ → Integrable (fun ω => ℓ θ (X 0 ω)) P)
    (hlt : ∀ θ ∈ K, θ ≠ θ₀ → popCrit P ℓ X θ < popCrit P ℓ X θ₀)
    (hloc : ∀ θ ∈ K, θ ≠ θ₀ → HasLocalEnvelope P S ℓ X θ) {uT : α → ℝ}
    (huT : Measurable uT) (hintT : Integrable (fun ω => uT (X 0 ω)) P)
    (henvT : ∀ θ ∈ S \ K, ∀ x, ℓ θ x ≤ uT x) (hltT : ∫ ω, uT (X 0 ω) ∂P < popCrit P ℓ X θ₀)
    {ε : ℝ} (hε : 0 < ε) : ∃ C, IsWaldCover P ℓ X S θ₀ ε C := by
  set T : Set Θ := K \ ball θ₀ ε
  have hT : IsCompact T := hK.diff isOpen_ball
  have hne : ∀ θ ∈ T, θ ≠ θ₀ := fun θ hθ h => hθ.2 (h ▸ mem_ball_self hε)
  have hb : ∀ θ : T, ∃ r > 0, ∃ u : α → ℝ, Measurable u ∧ Integrable (fun ω => u (X 0 ω)) P ∧
      (∀ θ' ∈ S, dist θ' θ < r → ∀ x, ℓ θ' x ≤ u x) ∧
      ∫ ω, u (X 0 ω) ∂P < popCrit P ℓ X θ₀ := fun θ =>
    exists_ball_envelope_lt hX (hloc θ θ.2.1 (hne θ θ.2)) (hint θ θ.2.1 (hne θ θ.2))
      (hlt θ θ.2.1 (hne θ θ.2))
  choose r hr u hu using hb
  obtain ⟨t, ht⟩ := hT.elim_finite_subcover (fun θ : T => ball (θ : Θ) (r θ))
    (fun _ => isOpen_ball) fun θ hθ => Set.mem_iUnion.2 ⟨⟨θ, hθ⟩, mem_ball_self (hr _)⟩
  refine ⟨((fun θ : T => (S ∩ ball (θ : Θ) (r θ), u θ)) '' (t : Set T)) ∪ {(S \ K, uT)},
    (t.finite_toSet.image _).union (Set.finite_singleton _), ?_, ?_⟩
  · intro θ hθ
    by_cases hθK : θ ∈ K
    · obtain ⟨i, hit, hθi⟩ := Set.mem_iUnion₂.1 (ht ⟨hθK, hθ.2⟩)
      exact Set.mem_iUnion₂.2 ⟨_, Or.inl ⟨i, hit, rfl⟩, hθ.1, hθi⟩
    · exact Set.mem_iUnion₂.2 ⟨_, Or.inr rfl, hθ.1, hθK⟩
  · rintro p (⟨i, -, rfl⟩ | hp)
    · exact ⟨(hu i).1, (hu i).2.1, fun θ' hθ' => (hu i).2.2.1 θ' hθ'.1 (mem_ball.1 hθ'.2),
        (hu i).2.2.2⟩
    · rw [Set.mem_singleton_iff.1 hp]
      exact ⟨huT, hintT, henvT, hltT⟩

/-- **Wald consistency on a compact parameter set from local envelopes**, almost surely. Let `K`
be compact, the population criterion have the unique maximizer `θ₀` on `K`, `ℓ θ (X 0)` be
integrable for every `θ ∈ K`, local envelopes exist at every `θ ∈ K` other than `θ₀`, and the
observations be pairwise independent and identically distributed. Then every MLE on `K`
converges to `θ₀` almost surely. Unlike `MLEConsistency.ae_tendsto_of_isMLEOn`, no uniform law of
large numbers and no continuity of `θ ↦ ℓ θ x` is assumed. -/
theorem ae_tendsto_of_isMLEOn_of_hasLocalEnvelope [IsProbabilityMeasure P] {K : Set Θ}
    (hK : IsCompact K) {ℓ : Θ → α → ℝ} {X : ℕ → Ω → α} {θ₀ : Θ}
    (hId : IsIdentifiedOn K (popCrit P ℓ X) θ₀) (hℓ₀ : Measurable (ℓ θ₀))
    (hint : ∀ θ ∈ K, Integrable (fun ω => ℓ θ (X 0 ω)) P)
    (hloc : ∀ θ ∈ K, θ ≠ θ₀ → HasLocalEnvelope P K ℓ X θ)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {est : ℕ → Ω → Θ} (hest : IsMLEOn K ℓ X est) :
    ∀ᵐ ω ∂P, Tendsto (fun n => est n ω) atTop (𝓝 θ₀) := by
  refine ae_tendsto_of_isMLEOn_of_isWaldCover hℓ₀ (hint θ₀ hId.1) hindep hident hId.1
    (fun ε hε => exists_isWaldCover hK (hident 0).aemeasurable_fst
      (fun θ hθ _ => hint θ hθ) (fun θ hθ hne => hId.2 θ hθ hne) hloc
      (uT := fun _ => popCrit P ℓ X θ₀ - 1) measurable_const (integrable_const _)
      (fun θ hθ => absurd hθ.1 hθ.2) ?_ hε) hest
  simp

end Local

/-! ## Wald's theorem: closed parameter sets in proper spaces -/

section Tail

/-- **The envelope at infinity has small mean far out.** From an envelope at infinity `v`, some
`n` and some integrable envelope of `ℓ θ` for every `θ ∈ S` at distance `> n` from `θc` have mean
below `E ℓ θ₀ (X 0)`. The envelope is the truncation `max (v n) c` with
`c = E ℓ θ₀ (X 0) - 1`, whose mean tends to `c` by dominated convergence. -/
theorem exists_tail_envelope_lt [IsProbabilityMeasure P] {S : Set Θ} {ℓ : Θ → α → ℝ}
    {X : ℕ → Ω → α} (hX : AEMeasurable (X 0) P) {θc θ₀ : Θ}
    (htail : HasTailEnvelope P S ℓ X θc) :
    ∃ n : ℕ, ∃ u : α → ℝ, Measurable u ∧ Integrable (fun ω => u (X 0 ω)) P ∧
      (∀ θ ∈ S, (n : ℝ) < dist θ θc → ∀ x, ℓ θ x ≤ u x) ∧
      ∫ ω, u (X 0 ω) ∂P < popCrit P ℓ X θ₀ := by
  obtain ⟨v, hmeas, hint0, henv, hanti, hlim⟩ := htail
  set c : ℝ := popCrit P ℓ X θ₀ - 1
  have hbd : ∀ n x, ‖max (v n x) c‖ ≤ |v 0 x| + |c| := fun n x => by
    rw [Real.norm_eq_abs, abs_le]
    have h2 := hanti x (Nat.zero_le n)
    constructor
    · cases abs_cases (v 0 x) <;> cases abs_cases c <;> linarith [le_max_right (v n x) c]
    · rcases le_total (v n x) c with h | h
      · rw [max_eq_right h]; cases abs_cases (v 0 x) <;> cases abs_cases c <;> linarith
      · rw [max_eq_left h]; cases abs_cases (v 0 x) <;> cases abs_cases c <;> linarith
  have hmeas' : ∀ n, AEStronglyMeasurable (fun ω => max (v n (X 0 ω)) c) P := fun n =>
    (((hmeas n).max measurable_const).comp_aemeasurable hX).aestronglyMeasurable
  have hconv : Tendsto (fun n => ∫ ω, max (v n (X 0 ω)) c ∂P) atTop (𝓝 (∫ _ : Ω, c ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => |v 0 (X 0 ω)| + |c|) hmeas'
      (hint0.abs.add (integrable_const _)) (fun n => ae_of_all _ fun ω => hbd n (X 0 ω))
      (ae_of_all _ fun ω => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(hlim (X 0 ω)).eventually (eventually_le_atBot c)] with n hn
    exact (max_eq_right hn).symm
  have hc : ∫ _ : Ω, c ∂P < popCrit P ℓ X θ₀ := by simp [c]
  obtain ⟨n, hn⟩ := (hconv.eventually (gt_mem_nhds hc)).exists
  refine ⟨n, fun x => max (v n x) c, (hmeas n).max measurable_const, ?_,
    fun θ hθ hd x => (henv n θ hθ hd x).trans (le_max_left _ _), hn⟩
  exact Integrable.mono' (hint0.abs.add (integrable_const _)) (hmeas' n)
    (ae_of_all _ fun ω => hbd n (X 0 ω))

/-- **Wald's theorem (1949)**: consistency of the MLE on a closed parameter set in a proper space
(such as `ℝᵈ`), almost surely. Let `S` be closed, the population criterion have the unique
maximizer `θ₀` on `S`, `ℓ θ (X 0)` be integrable for every `θ ∈ S`, `ℓ θ₀` be measurable, local
envelopes exist at every `θ ∈ S` other than `θ₀`, an envelope at infinity exist around some centre
`θc`, and the observations be pairwise independent and identically distributed. Then every MLE
on `S` converges to `θ₀` almost surely. `S` need not be compact. -/
theorem ae_tendsto_of_isMLEOn_of_hasTailEnvelope [ProperSpace Θ] [IsProbabilityMeasure P]
    {S : Set Θ} (hS : IsClosed S) {ℓ : Θ → α → ℝ} {X : ℕ → Ω → α} {θ₀ θc : Θ}
    (hId : IsIdentifiedOn S (popCrit P ℓ X) θ₀) (hℓ₀ : Measurable (ℓ θ₀))
    (hint : ∀ θ ∈ S, Integrable (fun ω => ℓ θ (X 0 ω)) P)
    (hloc : ∀ θ ∈ S, θ ≠ θ₀ → HasLocalEnvelope P S ℓ X θ) (htail : HasTailEnvelope P S ℓ X θc)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {est : ℕ → Ω → Θ} (hest : IsMLEOn S ℓ X est) :
    ∀ᵐ ω ∂P, Tendsto (fun n => est n ω) atTop (𝓝 θ₀) := by
  have hX : AEMeasurable (X 0) P := (hident 0).aemeasurable_fst
  obtain ⟨n, u, hu, huint, huenv, hult⟩ := exists_tail_envelope_lt (θ₀ := θ₀) hX htail
  have hK : IsCompact (S ∩ closedBall θc n) := (isCompact_closedBall θc n).inter_left hS
  refine ae_tendsto_of_isMLEOn_of_isWaldCover hℓ₀ (hint θ₀ hId.1) hindep hident hId.1
    (fun ε hε => exists_isWaldCover hK hX (fun θ hθ _ => hint θ hθ.1)
      (fun θ hθ hne => hId.2 θ hθ.1 hne) (fun θ hθ hne => hloc θ hθ.1 hne) hu huint
      (fun θ hθ => huenv θ hθ.1 ?_) hult hε) hest
  by_contra h
  exact hθ.2 ⟨hθ.1, mem_closedBall.2 (not_lt.1 h)⟩

/-- **Wald's theorem in probability**: under the hypotheses of
`ae_tendsto_of_isMLEOn_of_hasTailEnvelope` and for an a.e. strongly measurable MLE,
`est n → θ₀` in probability, the consistent-root input of `EstimatedInformation`. -/
theorem tendstoInMeasure_of_isMLEOn_of_hasTailEnvelope [ProperSpace Θ] [IsProbabilityMeasure P]
    {S : Set Θ} (hS : IsClosed S) {ℓ : Θ → α → ℝ} {X : ℕ → Ω → α} {θ₀ θc : Θ}
    (hId : IsIdentifiedOn S (popCrit P ℓ X) θ₀) (hℓ₀ : Measurable (ℓ θ₀))
    (hint : ∀ θ ∈ S, Integrable (fun ω => ℓ θ (X 0 ω)) P)
    (hloc : ∀ θ ∈ S, θ ≠ θ₀ → HasLocalEnvelope P S ℓ X θ) (htail : HasTailEnvelope P S ℓ X θc)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {est : ℕ → Ω → Θ} (hest : IsMLEOn S ℓ X est)
    (hmeas : ∀ n, AEStronglyMeasurable (est n) P) :
    TendstoInMeasure P est atTop fun _ => θ₀ :=
  tendstoInMeasure_of_tendsto_ae hmeas
    (ae_tendsto_of_isMLEOn_of_hasTailEnvelope hS hId hℓ₀ hint hloc htail hindep hident hest)

end Tail

end MathlibExt.Probability.Statistics.WaldEnvelope
