/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DirichletProcess
public import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Count

/-!
# The GEM and Poisson–Dirichlet laws on sequences

The **GEM(θ)** law (`gemMeasure`) is the distribution of the stick-breaking weights
`stickWeight V` when the breaks `V k` are independent `Beta(1, θ)`: it is the image of the
Sethuraman stick-breaking measure `sethuraman θ hθ` under the weight map, its coordinates
have mean `(θ / (1 + θ))^k / (1 + θ)`, and almost every sequence under it sums to `1`.

`rankDesc p k` is the supremal `k`-th largest value of a real sequence `p` (its decreasing
rearrangement when the supremum is attained, e.g. for nonnegative summable `p`), defined
through the counting characterization
`t < rankDesc p k ↔ ((k + 1 : ℕ) : ℕ∞) ≤ {i | t < p i}.encard`. It is antitone, nonnegative on
nonnegative sequences, preserves `HasSum` (by the layer-cake formula: ranking preserves
every superlevel count), is invariant under permutations of the indices, and is measurable.

The **Poisson–Dirichlet law PD(θ)** (`pdMeasure`) is the image of `gemMeasure θ` under
`rankDesc`; almost every sequence under it is decreasing, nonnegative and sums to `1`.

Indexing is 0-based throughout, following `stickWeight`. Only the one-parameter family
PD(θ) is treated.

## References

* J. Pitman, *Combinatorial Stochastic Processes*, Lecture Notes in Math. 1875, Springer,
  2006, Ch. 3 (GEM and Poisson–Dirichlet distributions).
-/

@[expose] public section

open MeasureTheory Filter Finset Topology
open scoped ENNReal

namespace ProbabilityTheory

/-! ### GEM(θ) -/

/-- The **GEM(θ)** law (Griffiths–Engen–McCloskey) on sequences: the law of the stick-breaking
weights `P_k = W_k ∏_{j<k} (1 - W_j)` (Atlas `stickWeight`, indexed from `0`) for i.i.d.
`W_j ∼ Beta(1, θ)`. -/
noncomputable def gemMeasure (θ : ℝ) (hθ : 0 < θ) : Measure (ℕ → ℝ) :=
  haveI := isProbabilityMeasureBeta zero_lt_one hθ
  (Measure.infinitePi fun _ : ℕ => betaMeasure 1 θ).map fun b k => stickWeight b k

/-- The stick-breaking weight sequence depends measurably on the proportions. -/
theorem measurable_stickWeight_seq : Measurable fun (b : ℕ → ℝ) (k : ℕ) => stickWeight b k := by
  refine measurable_pi_iff.2 fun k => ?_
  unfold stickWeight stickRemainder
  fun_prop

/-- GEM(θ) is the law of the weights of Sethuraman's stick-breaking process (Atlas
`sethuraman`), for any base measure. -/
theorem gemMeasure_eq_map_sethuraman {X : Type*} [MeasurableSpace X] (θ : ℝ) (hθ : 0 < θ)
    (H : Measure X) [IsProbabilityMeasure H] :
    gemMeasure θ hθ =
      (sethuramanMeasure θ hθ H).map fun ω k => (sethuraman θ hθ H).weight k ω := by
  have := isProbabilityMeasureBeta zero_lt_one hθ
  have h : (fun ω k => (sethuraman θ hθ H).weight k ω) =
      (fun b k => stickWeight b k) ∘ Prod.fst := by
    funext ω k; rfl
  rw [h, ← Measure.map_map measurable_stickWeight_seq measurable_fst,
    (measurePreserving_fst_sethuramanMeasure hθ H).map_eq, gemMeasure]

/-- GEM(θ) is a probability measure. -/
instance isProbabilityMeasure_gemMeasure (θ : ℝ) (hθ : 0 < θ) :
    IsProbabilityMeasure (gemMeasure θ hθ) := by
  have := isProbabilityMeasureBeta zero_lt_one hθ
  exact (Measure.isProbabilityMeasure_map_iff measurable_stickWeight_seq.aemeasurable).2
    inferInstance

/-- **Mean GEM weights**: `E[P_k] = θ^k / (1 + θ)^(k+1)`; in particular `E[P_0] = 1 / (1 + θ)`
for the first weight (index `0` here). -/
theorem integral_gemMeasure_apply (θ : ℝ) (hθ : 0 < θ) (k : ℕ) :
    ∫ p, p k ∂gemMeasure θ hθ = θ ^ k / (1 + θ) ^ (k + 1) := by
  rw [gemMeasure_eq_map_sethuraman θ hθ (Measure.dirac ()),
    integral_map (measurable_pi_iff.2 fun j => (sethuraman θ hθ (Measure.dirac ())).measurable_weight j).aemeasurable
      (measurable_pi_apply k).aestronglyMeasurable]
  exact (StickBreakingProcess.isDirichlet_sethuraman θ hθ (Measure.dirac ())).integral_weight k

/-- The first GEM weight has mean `1 / (1 + θ)`. -/
theorem integral_gemMeasure_zero (θ : ℝ) (hθ : 0 < θ) :
    ∫ p, p 0 ∂gemMeasure θ hθ = 1 / (1 + θ) := by
  rw [integral_gemMeasure_apply]; simp

private theorem measurableSet_nonneg_tendsto_one :
    MeasurableSet ((⋂ k, {p : ℕ → ℝ | 0 ≤ p k}) ∩
      {p : ℕ → ℝ | Tendsto (fun n => ∑ k ∈ range n, p k) atTop (𝓝 1)}) :=
  (MeasurableSet.iInter fun k => measurableSet_le measurable_const (measurable_pi_apply k)).inter
    (measurableSet_tendsto (𝓝 1) fun n => Finset.measurable_sum (range n) fun k _ =>
      (measurable_pi_apply k : Measurable fun p : ℕ → ℝ => p k))

/-- **GEM weights are nonnegative and sum to `1` almost surely.** -/
theorem ae_hasSum_gemMeasure (θ : ℝ) (hθ : 0 < θ) :
    ∀ᵐ p ∂gemMeasure θ hθ, (∀ k, 0 ≤ p k) ∧ HasSum p 1 := by
  set P := sethuraman θ hθ (Measure.dirac ())
  have hmeas : Measurable fun ω k => P.weight k ω :=
    measurable_pi_iff.2 fun j => P.measurable_weight j
  have hS := measurableSet_nonneg_tendsto_one
  have h : ∀ᵐ p ∂gemMeasure θ hθ, p ∈ (⋂ k, {p : ℕ → ℝ | 0 ≤ p k}) ∩
      {p : ℕ → ℝ | Tendsto (fun n => ∑ k ∈ range n, p k) atTop (𝓝 1)} := by
    rw [gemMeasure_eq_map_sethuraman θ hθ (Measure.dirac ())]
    refine (ae_map_iff hmeas.aemeasurable hS).2 ?_
    filter_upwards [(StickBreakingProcess.isDirichlet_sethuraman θ hθ
      (Measure.dirac ())).ae_hasSum_weight, P.ae_weight_mem_Icc] with ω hsum hI
    exact ⟨Set.mem_iInter.2 fun k => (hI k).1, hsum.tendsto_sum_nat⟩
  filter_upwards [h] with p hp
  have h0 : ∀ k, 0 ≤ p k := fun k => Set.mem_iInter.1 hp.1 k
  exact ⟨h0, (hasSum_iff_tendsto_nat_of_nonneg h0 1).2 hp.2⟩

/-! ### Decreasing rearrangement and PD(θ) -/

/-- The **supremal `k`-th largest value** (counted with multiplicity, from `k = 0`) of a
sequence: the supremum over `(k + 1)`-element index sets `s` of `min_{i ∈ s} p i`. This is
in general a supremum, not an entry of `p` (e.g. `p n = 1 - 1 / (n + 1)` gives
`rankDesc p 0 = 1`, attained by no entry). For a nonnegative sequence tending to `0` the
supremum is attained and this is the `k`-th entry of the decreasing rearrangement, padded
with zeros when fewer than `k + 1` entries are positive. -/
noncomputable def rankDesc (p : ℕ → ℝ) (k : ℕ) : ℝ :=
  ⨆ s : {s : Finset ℕ // s.card = k + 1}, ⨅ i : s.1, p i

private theorem ciInf_fin_lt_iff {s : Finset ℕ} (hs : s.Nonempty) (p : ℕ → ℝ) (t : ℝ) :
    t < ⨅ i : s, p i ↔ ∀ i ∈ s, t < p i := by
  have : Nonempty s := hs.to_subtype
  constructor
  · intro h i hi
    exact h.trans_le (ciInf_le (Set.finite_range _).bddBelow (⟨i, hi⟩ : s))
  · intro h
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i : s => p i)
    rw [← hi]
    exact h i.1 i.2

private theorem bddAbove_inf (p : ℕ → ℝ) (hp : BddAbove (Set.range p)) (k : ℕ) :
    BddAbove (Set.range fun s : {s : Finset ℕ // s.card = k + 1} => ⨅ i : s.1, p i) := by
  obtain ⟨M, hM⟩ := hp
  refine ⟨M, ?_⟩
  rintro _ ⟨s, rfl⟩
  have hs : s.1.Nonempty := Finset.card_pos.1 (by rw [s.2]; exact Nat.succ_pos k)
  obtain ⟨i, hi⟩ := hs
  exact (ciInf_le (Set.finite_range _).bddBelow (⟨i, hi⟩ : s.1)).trans (hM ⟨i, rfl⟩)

/-- **The rank characterization.** For a sequence bounded above, `t < rankDesc p k` iff at
least `k + 1` entries exceed `t`. -/
theorem lt_rankDesc_iff {p : ℕ → ℝ} (hp : BddAbove (Set.range p)) (k : ℕ) (t : ℝ) :
    t < rankDesc p k ↔ ((k + 1 : ℕ) : ℕ∞) ≤ {i | t < p i}.encard := by
  have hne : Nonempty {s : Finset ℕ // s.card = k + 1} :=
    ⟨⟨range (k + 1), card_range _⟩⟩
  rw [rankDesc, lt_ciSup_iff (bddAbove_inf p hp k)]
  constructor
  · rintro ⟨s, hs⟩
    have hsne : s.1.Nonempty := Finset.card_pos.1 (by rw [s.2]; exact Nat.succ_pos k)
    rw [ciInf_fin_lt_iff hsne] at hs
    have hsub : (s.1 : Set ℕ) ⊆ {i | t < p i} := fun i hi => hs i hi
    calc ((k + 1 : ℕ) : ℕ∞) = (s.1 : Set ℕ).encard := by rw [Set.encard_coe_eq_coe_finsetCard, s.2]
      _ ≤ _ := Set.encard_le_encard hsub
  · intro h
    obtain ⟨u, hu, hcard⟩ := Set.exists_subset_encard_eq h
    have hfin : u.Finite := Set.finite_of_encard_eq_coe hcard
    refine ⟨⟨hfin.toFinset, ?_⟩, ?_⟩
    · have := hfin.encard_eq_coe_toFinset_card
      rw [hcard] at this
      exact_mod_cast this.symm
    · have hsne : hfin.toFinset.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty, ne_eq, Set.Finite.toFinset_eq_empty]
        rintro rfl
        simp only [Set.encard_empty] at hcard
        exact absurd hcard.symm (by simp)
      rw [ciInf_fin_lt_iff hsne]
      intro i hi
      exact hu ((Set.Finite.mem_toFinset hfin).1 hi)

/-- The ranked sequence is decreasing. -/
theorem antitone_rankDesc {p : ℕ → ℝ} (hp : BddAbove (Set.range p)) : Antitone (rankDesc p) := by
  refine antitone_nat_of_succ_le fun k => ?_
  by_contra h
  push Not at h
  have h1 := (lt_rankDesc_iff hp (k + 1) (rankDesc p k)).1 h
  have h2 : ((k + 1 : ℕ) : ℕ∞) ≤ {i | rankDesc p k < p i}.encard :=
    le_trans (by exact_mod_cast Nat.le_succ (k + 1)) h1
  exact lt_irrefl _ ((lt_rankDesc_iff hp k (rankDesc p k)).2 h2)

/-- The ranked entries of a nonnegative sequence are nonnegative. -/
theorem rankDesc_nonneg {p : ℕ → ℝ} (hp : BddAbove (Set.range p)) (h0 : ∀ i, 0 ≤ p i)
    (k : ℕ) : 0 ≤ rankDesc p k := by
  refine le_of_forall_lt fun t ht => ?_
  rw [lt_rankDesc_iff hp]
  have : {i | t < p i} = Set.univ := Set.eq_univ_of_forall fun i => ht.trans_le (h0 i)
  rw [this, Set.encard_univ, ENat.card_eq_top_of_infinite]
  exact le_top

/-- Each ranked entry depends measurably on the sequence. -/
theorem measurable_rankDesc (k : ℕ) : Measurable fun p : ℕ → ℝ => rankDesc p k := by
  unfold rankDesc
  refine Measurable.iSup fun s => Measurable.iInf fun i => measurable_pi_apply _

/-- The counting function of the ranked sequence equals that of the sequence. -/
theorem encard_lt_rankDesc {p : ℕ → ℝ} (hp : BddAbove (Set.range p)) (t : ℝ) :
    {k | t < rankDesc p k}.encard = {i | t < p i}.encard := by
  set E := {i | t < p i}.encard with hE
  have hset : {k | t < rankDesc p k} = {k : ℕ | ((k + 1 : ℕ) : ℕ∞) ≤ E} := by
    ext k; exact lt_rankDesc_iff hp k t
  rw [hset]
  by_cases htop : E = ⊤
  · rw [htop]
    have : {k : ℕ | ((k + 1 : ℕ) : ℕ∞) ≤ ⊤} = Set.univ :=
      Set.eq_univ_of_forall fun k => (le_top : ((k + 1 : ℕ) : ℕ∞) ≤ ⊤)
    rw [this, Set.encard_univ, ENat.card_eq_top_of_infinite]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
    rw [← hn]
    have : {k : ℕ | ((k + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞)} = ((Finset.range n : Finset ℕ) : Set ℕ) := by
      ext k
      simp only [Set.mem_ofPred_eq, Nat.cast_le, Finset.coe_range, Set.mem_Iio]
      omega
    rw [this, Set.encard_coe_eq_coe_finsetCard, Finset.card_range]

/-- **Ranking preserves the total mass**: for a nonnegative summable sequence, the ranked
sequence is summable with the same sum. -/
theorem hasSum_rankDesc {p : ℕ → ℝ} (h0 : ∀ i, 0 ≤ p i) (hs : Summable p) :
    HasSum (rankDesc p) (∑' i, p i) := by
  have hb : BddAbove (Set.range p) := hs.tendsto_atTop_zero.bddAbove_range
  have hr0 := rankDesc_nonneg hb h0
  have key : ∑' k, ENNReal.ofReal (rankDesc p k) = ∑' i, ENNReal.ofReal (p i) := by
    have hl1 := lintegral_eq_lintegral_meas_lt Measure.count (f := rankDesc p)
      (ae_of_all _ hr0) (Measurable.of_discrete).aemeasurable
    have hl2 := lintegral_eq_lintegral_meas_lt Measure.count (f := p)
      (ae_of_all _ h0) (Measurable.of_discrete).aemeasurable
    rw [lintegral_count] at hl1 hl2
    rw [hl1, hl2]
    congr 1
    funext t
    rw [Measure.count_apply (MeasurableSet.of_discrete), Measure.count_apply
      (MeasurableSet.of_discrete), encard_lt_rankDesc hb]
  have hS : ∑' i, ENNReal.ofReal (p i) = ENNReal.ofReal (∑' i, p i) :=
    (ENNReal.ofReal_tsum_of_nonneg h0 hs).symm
  have hne : ∑' k, ENNReal.ofReal (rankDesc p k) ≠ ⊤ := by
    rw [key, hS]; exact ENNReal.ofReal_ne_top
  have hsumr : Summable (rankDesc p) := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hr0 _)] using this
  have heq : ∑' k, rankDesc p k = ∑' i, p i := by
    have h1 := (ENNReal.ofReal_tsum_of_nonneg hr0 hsumr).symm
    rw [key, hS] at h1
    exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hr0) (tsum_nonneg h0)).1 h1.symm
  rw [← heq]
  exact hsumr.hasSum

/-- **Ranking an already decreasing sequence returns it.** -/
theorem rankDesc_of_antitone {p : ℕ → ℝ} (hp : Antitone p) : rankDesc p = p := by
  have hb : BddAbove (Set.range p) := ⟨p 0, by rintro _ ⟨i, rfl⟩; exact hp (Nat.zero_le i)⟩
  funext k
  have key : ∀ t, t < rankDesc p k ↔ t < p k := by
    intro t
    rw [lt_rankDesc_iff hb]
    constructor
    · intro h
      by_contra hle
      push Not at hle
      have hsub : {i | t < p i} ⊆ ((Finset.range k : Finset ℕ) : Set ℕ) := by
        intro i hi
        simp only [Finset.coe_range, Set.mem_Iio]
        by_contra hik
        push Not at hik
        exact absurd (lt_of_lt_of_le hi (hp hik)) (not_lt.2 hle)
      have := (Set.encard_le_encard hsub).trans_eq' (by rfl)
      rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_range] at this
      have := h.trans this
      exact absurd (by exact_mod_cast this : k + 1 ≤ k) (by omega)
    · intro h
      have hsub : ((Finset.range (k + 1) : Finset ℕ) : Set ℕ) ⊆ {i | t < p i} := by
        intro i hi
        simp only [Finset.coe_range, Set.mem_Iio] at hi
        exact lt_of_lt_of_le h (hp (by omega))
      have := Set.encard_le_encard hsub
      rwa [Set.encard_coe_eq_coe_finsetCard, Finset.card_range] at this
  rcases lt_trichotomy (rankDesc p k) (p k) with h | h | h
  · exact absurd ((key _).2 h) (lt_irrefl _)
  · exact h
  · exact absurd ((key _).1 h) (lt_irrefl _)


/-- **Ranking forgets the order**: permuting the entries does not change the ranked sequence. -/
theorem rankDesc_comp_equiv {p : ℕ → ℝ} (hp : BddAbove (Set.range p)) (σ : ℕ ≃ ℕ) :
    rankDesc (p ∘ σ) = rankDesc p := by
  have hpσ : BddAbove (Set.range (p ∘ σ)) := by rwa [Set.range_comp, σ.range_eq_univ, Set.image_univ]
  funext k
  have key : ∀ t, t < rankDesc (p ∘ σ) k ↔ t < rankDesc p k := by
    intro t
    rw [lt_rankDesc_iff hpσ, lt_rankDesc_iff hp]
    have : {i | t < (p ∘ σ) i} = σ.symm '' {j | t < p j} := by
      ext i
      simp only [Set.mem_ofPred_eq, Function.comp_apply, Set.mem_image]
      constructor
      · intro h; exact ⟨σ i, h, σ.symm_apply_apply i⟩
      · rintro ⟨j, hj, rfl⟩; simpa using hj
    rw [this, σ.symm.injective.encard_image]
  rcases lt_trichotomy (rankDesc (p ∘ σ) k) (rankDesc p k) with h | h | h
  · exact absurd ((key _).2 h) (lt_irrefl _)
  · exact h
  · exact absurd ((key _).1 h) (lt_irrefl _)

/-- The **Poisson–Dirichlet law PD(θ)**: the law of the decreasing rearrangement of a GEM(θ)
sequence. -/
noncomputable def pdMeasure (θ : ℝ) (hθ : 0 < θ) : Measure (ℕ → ℝ) :=
  (gemMeasure θ hθ).map fun p k => rankDesc p k

/-- The ranking map is measurable. -/
theorem measurable_rankDesc_seq : Measurable fun (p : ℕ → ℝ) (k : ℕ) => rankDesc p k :=
  measurable_pi_iff.2 measurable_rankDesc

/-- PD(θ) is a probability measure. -/
instance isProbabilityMeasure_pdMeasure (θ : ℝ) (hθ : 0 < θ) :
    IsProbabilityMeasure (pdMeasure θ hθ) :=
  (Measure.isProbabilityMeasure_map_iff measurable_rankDesc_seq.aemeasurable).2 inferInstance

private theorem measurableSet_ranked :
    MeasurableSet ((⋂ k, {p : ℕ → ℝ | p (k + 1) ≤ p k}) ∩ (⋂ k, {p : ℕ → ℝ | 0 ≤ p k}) ∩
      {p : ℕ → ℝ | Tendsto (fun n => ∑ k ∈ range n, p k) atTop (𝓝 1)}) :=
  ((MeasurableSet.iInter fun k => measurableSet_le
      (measurable_pi_apply (k + 1) : Measurable fun p : ℕ → ℝ => p (k + 1))
      (measurable_pi_apply k)).inter
    (MeasurableSet.iInter fun k => measurableSet_le measurable_const
      (measurable_pi_apply k : Measurable fun p : ℕ → ℝ => p k))).inter
    (measurableSet_tendsto (𝓝 1) fun n => Finset.measurable_sum (range n) fun k _ =>
      (measurable_pi_apply k : Measurable fun p : ℕ → ℝ => p k))

/-- **PD(θ)-almost every sequence is decreasing, nonnegative and sums to `1`.** -/
theorem ae_pdMeasure (θ : ℝ) (hθ : 0 < θ) :
    ∀ᵐ p ∂pdMeasure θ hθ, Antitone p ∧ (∀ k, 0 ≤ p k) ∧ HasSum p 1 := by
  have h : ∀ᵐ p ∂pdMeasure θ hθ, p ∈ (⋂ k, {p : ℕ → ℝ | p (k + 1) ≤ p k}) ∩
      (⋂ k, {p : ℕ → ℝ | 0 ≤ p k}) ∩
      {p : ℕ → ℝ | Tendsto (fun n => ∑ k ∈ range n, p k) atTop (𝓝 1)} := by
    refine (ae_map_iff measurable_rankDesc_seq.aemeasurable measurableSet_ranked).2 ?_
    filter_upwards [ae_hasSum_gemMeasure θ hθ] with p ⟨h0, hsum⟩
    have hb : BddAbove (Set.range p) := hsum.summable.tendsto_atTop_zero.bddAbove_range
    have hr := hasSum_rankDesc h0 hsum.summable
    rw [hsum.tsum_eq] at hr
    refine ⟨⟨Set.mem_iInter.2 fun k => antitone_rankDesc hb (Nat.le_succ k),
      Set.mem_iInter.2 fun k => rankDesc_nonneg hb h0 k⟩, hr.tendsto_sum_nat⟩
  filter_upwards [h] with p hp
  have h0 : ∀ k, 0 ≤ p k := fun k => Set.mem_iInter.1 hp.1.2 k
  exact ⟨antitone_nat_of_succ_le fun k => Set.mem_iInter.1 hp.1.1 k, h0,
    (hasSum_iff_tendsto_nat_of_nonneg h0 1).2 hp.2⟩

end ProbabilityTheory
