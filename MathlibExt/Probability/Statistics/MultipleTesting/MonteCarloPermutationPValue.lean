/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.PermutationPValue
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.UniformOn

/-!
# Monte Carlo permutation p-values are valid

Let a finite group `G` act on the sample space `Ω`, let the null law `μ` be `G`-invariant, and
let `g₁, …, g_B` be drawn independently and uniformly from `G` (with replacement),
independently of the data `ω`. The Monte Carlo permutation p-value of a statistic `T` is

`p(ω, g) = (1 + #{b | T(g_b • ω) ≥ T(ω)}) / (B + 1)`.

Counting the observed statistic as one of the `B + 1` draws makes `p` valid under the joint law
`μ ⊗ Unif(G)^B`: `P(p ≤ α) ≤ α` for every `α ∈ [0, 1]` (Phipson and Smyth 2010; Hemerik and
Goeman 2018). The proof is the exchangeability argument written as finite sums: for
every fixed `h ∈ G`, `(h • ω, g₁ h⁻¹, …, g_B h⁻¹)` has the same joint law as `(ω, g₁, …, g_B)`
(invariance of `μ` and of the uniform law), so the observed statistic may be placed at any of the
`B + 1` positions of `(T(k₀ • ω), …, T(k_B • ω))`, `k` uniform on `G^{B+1}`; averaging over
the positions, the rank-counting lemma `card_filter_rankCount_le` bounds the rejection
probability by `α`.

The draws are with replacement and may include the identity; the bound does not need them to
be distinct. With `B = 0` the p-value is identically `1`.

## Main results

* `isValidPValue_monteCarloPermutationPValue`.

## References

* B. Phipson and G. K. Smyth, *Permutation p-values should never be zero*, Stat. Appl. Genet.
  Mol. Biol. 9 (2010), Article 39.
* J. Hemerik and J. Goeman, *Exact testing with random permutations*, TEST 27 (2018),
  811–825.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {G : Type*} [Group G] [MulAction G Ω]

/-- The Monte Carlo permutation p-value `(1 + #{b | T(g_b • ω) ≥ T(ω)}) / (B + 1)` of the
statistic `T` at the data `ω` with the `B` drawn group elements `g`. -/
noncomputable def monteCarloPermutationPValue {B : ℕ} (T : Ω → ℝ) (ω : Ω) (g : Fin B → G) :
    ℝ :=
  (1 + ((Finset.univ.filter fun b => T ω ≤ T (g b • ω)).card : ℝ)) / (B + 1)

/-- `#{i | T(k_j • ω) ≤ T(k_i • ω)}`: how many of the `n` transformed statistics are at least the
`j`-th one. -/
private noncomputable def rankCount {Ω G : Type*} [SMul G Ω] {n : ℕ} (T : Ω → ℝ) (ω : Ω)
    (k : Fin n → G) (j : Fin n) : ℕ :=
  (Finset.univ.filter fun i => T (k j • ω) ≤ T (k i • ω)).card

private theorem rankCount_cons {Ω G : Type*} [SMul G Ω] {B : ℕ} (T : Ω → ℝ) (ω : Ω) (h : G)
    (g : Fin B → G) :
    rankCount T ω (Fin.cons h g : Fin (B + 1) → G) 0 =
      1 + (Finset.univ.filter fun b => T (h • ω) ≤ T (g b • ω)).card := by
  simp only [rankCount, Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    le_refl, ite_true]

private theorem rankCount_swap {Ω G : Type*} [SMul G Ω] {n : ℕ} (T : Ω → ℝ) (ω : Ω)
    (k : Fin (n + 1) → G) (j : Fin (n + 1)) :
    rankCount T ω (k ∘ Equiv.swap 0 j) 0 = rankCount T ω k j := by
  simp only [rankCount, Finset.card_filter, Function.comp_apply, Equiv.swap_apply_left]
  exact Equiv.sum_comp (Equiv.swap 0 j) (fun i => if T (k j • ω) ≤ T (k i • ω) then 1 else 0)

private theorem measurable_rankCount {Ω G : Type*} [MeasurableSpace Ω] [SMul G Ω] {n : ℕ}
    (hsmul : ∀ g : G, Measurable fun ω : Ω => g • ω) {T : Ω → ℝ} (hT : Measurable T)
    (k : Fin n → G) (j : Fin n) :
    Measurable fun ω => (rankCount T ω k j : ℝ) := by
  have h : ∀ ω, (rankCount T ω k j : ℝ) =
      ∑ i, Set.indicator {ω | T (k j • ω) ≤ T (k i • ω)} (fun _ => (1 : ℝ)) ω := by
    intro ω
    simp [rankCount, Set.indicator_apply, Finset.sum_boole]
  simp_rw [h]
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator
    (measurableSet_le (hT.comp (hsmul _)) (hT.comp (hsmul _)))

private theorem mcPValue_le_iff {Ω G : Type*} [Group G] [MulAction G Ω] {B : ℕ} (T : Ω → ℝ) (ω : Ω)
    (g : Fin B → G) (t : ℝ) :
    monteCarloPermutationPValue T ω g ≤ t ↔
      ((1 + (Finset.univ.filter fun b => T ω ≤ T (g b • ω)).card : ℕ) : ℝ) ≤ t * (B + 1) := by
  rw [monteCarloPermutationPValue, div_le_iff₀ (by positivity)]
  push_cast
  rfl

private theorem measurable_mcPValue {Ω G : Type*} [MeasurableSpace Ω] [Group G] [MulAction G Ω]
    {B : ℕ}
    (hsmul : ∀ g : G, Measurable fun ω : Ω => g • ω) {T : Ω → ℝ} (hT : Measurable T)
    (g : Fin B → G) : Measurable fun ω => monteCarloPermutationPValue T ω g := by
  have h : ∀ ω, ((Finset.univ.filter fun b => T ω ≤ T (g b • ω)).card : ℝ) =
      ∑ b, Set.indicator {ω | T ω ≤ T (g b • ω)} (fun _ => (1 : ℝ)) ω := by
    intro ω
    simp [Set.indicator_apply, Finset.sum_boole]
  unfold monteCarloPermutationPValue
  simp_rw [h]
  refine Measurable.div_const (measurable_const.add (Finset.measurable_sum _ fun b _ => ?_)) _
  exact measurable_const.indicator (measurableSet_le hT (hT.comp (hsmul _)))

private theorem sum_measure_eq_sum_rankCount {Ω G : Type*} [MeasurableSpace Ω] [Group G] [Fintype G]
    [MulAction G Ω] {B : ℕ} (μ : Measure Ω) [SMulInvariantMeasure G Ω μ]
    (hsmul : ∀ g : G, Measurable fun ω : Ω => g • ω) {T : Ω → ℝ} (hT : Measurable T) (t : ℝ)
    (h : G) :
    ∑ g : Fin B → G, μ {ω | monteCarloPermutationPValue T ω g ≤ t} =
      ∑ g : Fin B → G, μ {ω | (rankCount T ω (Fin.cons h g : Fin (B + 1) → G) 0 : ℝ) ≤
        t * (B + 1)} := by
  let e : (Fin B → G) ≃ (Fin B → G) := Equiv.piCongrRight fun _ => Equiv.mulRight h⁻¹
  rw [← Fintype.sum_equiv e _ _ fun _ => rfl]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hS : MeasurableSet {ω | monteCarloPermutationPValue T ω (e g) ≤ t} :=
    measurableSet_le (measurable_mcPValue hsmul hT _) measurable_const
  rw [← SMulInvariantMeasure.measure_preimage_smul h hS]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, mcPValue_le_iff, rankCount_cons, e,
    Equiv.piCongrRight_apply, Equiv.coe_mulRight, Pi.map_apply, mul_smul, inv_smul_smul]

private theorem sum_measure_rankCount_le {Ω G : Type*} [MeasurableSpace Ω] [SMul G Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hsmul : ∀ g : G, Measurable fun ω : Ω => g • ω) {T : Ω → ℝ} (hT : Measurable T) {c : ℝ}
    (hc : 0 ≤ c) (k : Fin n → G) :
    ∑ j, μ {ω | (rankCount T ω k j : ℝ) ≤ c} ≤ ENNReal.ofReal c := by
  have hR : ∀ j, MeasurableSet {ω | (rankCount T ω k j : ℝ) ≤ c} := fun j =>
    measurableSet_le (measurable_rankCount hsmul hT k j) measurable_const
  have hpt : ∀ ω, (∑ j, {ω | (rankCount T ω k j : ℝ) ≤ c}.indicator (fun _ => (1 : ENNReal)) ω)
      ≤ ENNReal.ofReal c := by
    intro ω
    have hcount : (Finset.univ.filter fun j => ω ∈ {ω | (rankCount T ω k j : ℝ) ≤ c}).card ≤
        ⌊c⌋₊ := by
      refine le_trans (Finset.card_le_card fun j hj => ?_)
        (card_filter_rankCount_le (Fin n) (fun i => T (k i • ω)) ⌊c⌋₊)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj ⊢
      exact Nat.le_floor hj
    calc (∑ j, {ω | (rankCount T ω k j : ℝ) ≤ c}.indicator (fun _ => (1 : ENNReal)) ω)
        = ((Finset.univ.filter fun j => ω ∈ {ω | (rankCount T ω k j : ℝ) ≤ c}).card :
            ENNReal) := by
          rw [Finset.card_filter]
          push_cast
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hj : ω ∈ {ω | (rankCount T ω k j : ℝ) ≤ c} <;> simp [hj]
      _ ≤ (⌊c⌋₊ : ENNReal) := by exact_mod_cast hcount
      _ ≤ ENNReal.ofReal c := by
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (Nat.floor_le hc)
  calc ∑ j, μ {ω | (rankCount T ω k j : ℝ) ≤ c}
      = ∫⁻ ω, ∑ j, {ω | (rankCount T ω k j : ℝ) ≤ c}.indicator (fun _ => (1 : ENNReal)) ω ∂μ := by
        rw [lintegral_finsetSum _ fun j _ => measurable_const.indicator (hR j)]
        simp_rw [lintegral_indicator_const (hR _), one_mul]
    _ ≤ ∫⁻ _, ENNReal.ofReal c ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal c := by simp

private theorem sum_sum_measure_rankCount {Ω G : Type*} [MeasurableSpace Ω] [SMul G Ω] [Fintype G]
    {n : ℕ} (μ : Measure Ω) (T : Ω → ℝ) (c : ℝ) :
    ∑ k : Fin (n + 1) → G, ∑ j, μ {ω | (rankCount T ω k j : ℝ) ≤ c} =
      (n + 1 : ENNReal) * ∑ k : Fin (n + 1) → G, μ {ω | (rankCount T ω k 0 : ℝ) ≤ c} := by
  rw [Finset.sum_comm]
  have h : ∀ j : Fin (n + 1), ∑ k : Fin (n + 1) → G, μ {ω | (rankCount T ω k j : ℝ) ≤ c} =
      ∑ k : Fin (n + 1) → G, μ {ω | (rankCount T ω k 0 : ℝ) ≤ c} := by
    intro j
    let e : (Fin (n + 1) → G) ≃ (Fin (n + 1) → G) := (Equiv.swap 0 j).arrowCongr (Equiv.refl G)
    refine Fintype.sum_equiv e _ _ fun k => ?_
    have he : e k = k ∘ Equiv.swap 0 j := by
      ext i
      simp [e, Equiv.arrowCongr_apply]
    rw [he]
    simp_rw [rankCount_swap]
  simp_rw [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- Phipson and Smyth (2010); Hemerik and Goeman (2018): if the null law `μ` is invariant under
a finite group `G` and `g₁, …, g_B` are drawn independently and uniformly from `G`,
independently of the data, then `(1 + #{b | T(g_b • ω) ≥ T(ω)}) / (B + 1)` is a valid p-value
under the joint law. -/
theorem isValidPValue_monteCarloPermutationPValue [Finite G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G] (B : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G Ω μ] (hsmul : ∀ g : G, Measurable fun ω : Ω => g • ω) {T : Ω → ℝ}
    (hT : Measurable T) :
    IsValidPValue (μ.prod (Measure.pi fun _ : Fin B => uniformOn (Set.univ : Set G)))
      (fun x => monteCarloPermutationPValue T x.1 x.2) := by
  classical
  have := Fintype.ofFinite G
  intro t ht
  set N := Fintype.card G
  set ν := Measure.pi fun _ : Fin B => uniformOn (Set.univ : Set G)
  set Sg : (Fin B → G) → Set Ω := fun g => {ω | monteCarloPermutationPValue T ω g ≤ t}
  have hSg : ∀ g, MeasurableSet (Sg g) := fun g =>
    measurableSet_le (measurable_mcPValue hsmul hT g) measurable_const
  have hN0 : (N : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hNt : (N : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top N
  -- the joint probability as a finite sum over the draws
  have hν : ∀ g : Fin B → G, ν {g} = (N : ENNReal)⁻¹ ^ B := by
    intro g
    simp [ν, Measure.pi_singleton, uniformOn_univ, N]
  have hunion : {x : Ω × (Fin B → G) | monteCarloPermutationPValue T x.1 x.2 ≤ t} =
      ⋃ g, Sg g ×ˢ {g} := by
    ext x
    simp [Sg]
  have hP : (μ.prod ν) {x : Ω × (Fin B → G) | monteCarloPermutationPValue T x.1 x.2 ≤ t} =
      (N : ENNReal)⁻¹ ^ B * ∑ g, μ (Sg g) := by
    rw [hunion, measure_iUnion, tsum_fintype, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun g _ => ?_
      rw [Measure.prod_prod, hν, mul_comm]
    · intro g g' hgg'
      refine Set.disjoint_left.2 fun x hx hx' => hgg' ?_
      exact (Set.mem_singleton_iff.1 (Set.mem_prod.1 hx).2).symm.trans
        (Set.mem_singleton_iff.1 (Set.mem_prod.1 hx').2)
    · exact fun g => (hSg g).prod (measurableSet_singleton g)
  -- exchangeability bound
  set c := t * (B + 1)
  have hc : 0 ≤ c := mul_nonneg ht.1 (by positivity)
  have h3 : (N : ENNReal) * ∑ g, μ (Sg g) =
      ∑ k : Fin (B + 1) → G, μ {ω | (rankCount T ω k 0 : ℝ) ≤ c} := by
    calc (N : ENNReal) * ∑ g, μ (Sg g) = ∑ _h : G, ∑ g, μ (Sg g) := by
          simp [Finset.sum_const, N]
      _ = ∑ h : G, ∑ g : Fin B → G,
            μ {ω | (rankCount T ω (Fin.cons h g : Fin (B + 1) → G) 0 : ℝ) ≤ c} :=
          Finset.sum_congr rfl fun h _ => sum_measure_eq_sum_rankCount μ hsmul hT t h
      _ = ∑ k : Fin (B + 1) → G, μ {ω | (rankCount T ω k 0 : ℝ) ≤ c} := by
          rw [← Fintype.sum_prod_type']
          exact Fintype.sum_equiv (Fin.consEquiv fun _ => G) _ _ fun _ => rfl
  have h45 : (B + 1 : ENNReal) * ((N : ENNReal) * ∑ g, μ (Sg g)) ≤
      (N : ENNReal) ^ (B + 1) * ENNReal.ofReal c := by
    rw [h3, ← sum_sum_measure_rankCount]
    calc ∑ k : Fin (B + 1) → G, ∑ j, μ {ω | (rankCount T ω k j : ℝ) ≤ c}
        ≤ ∑ _k : Fin (B + 1) → G, ENNReal.ofReal c :=
          Finset.sum_le_sum fun k _ => sum_measure_rankCount_le μ hsmul hT hc k
      _ = (N : ENNReal) ^ (B + 1) * ENNReal.ofReal c := by
          simp [Finset.sum_const, N]
  have hB0 : (B + 1 : ENNReal) ≠ 0 := by positivity
  have hBt : (B + 1 : ENNReal) ≠ ⊤ := by simp
  have hsum : ∑ g, μ (Sg g) ≤ (N : ENNReal) ^ B * ENNReal.ofReal t := by
    have hofc : ENNReal.ofReal c = (B + 1 : ENNReal) * ENNReal.ofReal t := by
      rw [show c = (B + 1 : ℝ) * t by ring, ENNReal.ofReal_mul (by positivity)]
      norm_cast
    rw [hofc] at h45
    have : (B + 1 : ENNReal) * ((N : ENNReal) * ∑ g, μ (Sg g)) ≤
        (B + 1 : ENNReal) * ((N : ENNReal) * ((N : ENNReal) ^ B * ENNReal.ofReal t)) := by
      calc _ ≤ _ := h45
        _ = _ := by ring
    have h' := (ENNReal.mul_le_mul_iff_right hB0 hBt).1 this
    exact (ENNReal.mul_le_mul_iff_right hN0 hNt).1 h'
  change (μ.prod ν) {x : Ω × (Fin B → G) | monteCarloPermutationPValue T x.1 x.2 ≤ t} ≤ _
  rw [hP]
  calc (N : ENNReal)⁻¹ ^ B * ∑ g, μ (Sg g)
      ≤ (N : ENNReal)⁻¹ ^ B * ((N : ENNReal) ^ B * ENNReal.ofReal t) := by gcongr
    _ = ENNReal.ofReal t := by
        rw [← mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel hN0 hNt, one_pow, one_mul]

end MathlibExt.Probability.Statistics.MultipleTesting
