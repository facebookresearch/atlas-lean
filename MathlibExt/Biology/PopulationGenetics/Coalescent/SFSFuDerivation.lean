/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFuClosedForm
import Mathlib.Probability.Independence.Integration

/-!
# Branch-length covariances of the SFS from random joining and Kingman holding times

**Source.** Y.-X. Fu (1995), *Statistical properties of segregating sites*, Theor. Popul. Biol.
48, 172–197, Section 3: under Kingman's coalescent the total length `L_i` of the branches
subtending `i` of the `n` sample copies satisfies `Cov(L_i, L_j) = 4 σ_{ij}` with Fu's closed
form `σ_{ij}`. Fu derives this from the joint second moments of the block counts of the random
tree topology and the independent exponential holding times.

**Source receipt (API-00).** Reused, not reproved:

* `SiteFrequencySpectrum.randomJoining`, `joinStep`, `sfsLength`, `exists_finset_randomJoining`
  (merged): the law of the block-size history, its transition operator and `L_i`;
* `KingmanTimes` (merged, `Coalescent/Kingman.lean`): independent `Exp(C(k, 2))` holding times,
  with `KingmanTimes.integral_T` and `HasLaw.variance_eq_of_expMeasure`;
* `SFSCovariance.memLp_sfsLength` (merged): square integrability of `L_i`;
* `SFSFuClosedForm.fuSigma` and `covariance_count_kingman_of_fuSigma` (merged, T114): Fu's
  matrix and the SFS covariance conditional on the hypothesis `Cov(L_i, L_j) = 4 σ_{ij}`.

Proved here: the two-level Markov property of random joining
(`exists_finset_randomJoining_pair`), the second moments of the holding times
(`integral_T_mul_T`), and the factorization of `E[L_i L_j]` through the independence of the
topology and the holding times.

## What is proved

* `covariance_sfsLength_eq_fuTopologyCov`: for every sample size `n` and all `i, j`,
  `Cov(L_i, L_j) = fuTopologyCov n i j`, where
  `fuTopologyCov n i j = ∑_{k,l} E[c_{k,i} c_{l,j}] E[T_k T_l] - E[L_i] E[L_j]` is an explicit
  deterministic number: `c_{k,i}` is the number of blocks of size `i` while `k` lineages remain,
  its moments are iterates of the random-joining transition operator `joinStep`
  (`blockCountMean`, `blockCountMoment`), and `E[T_k T_l]` is `2 / C(k,2)²` on the diagonal and
  `1 / (C(k,2) C(l,2))` off it (`kingmanTimeMoment`). This discharges all of the probability in
  the hypothesis `hσ` of `SFSFuClosedForm`: independence of the topology and the holding times,
  independence and exponential laws of the holding times, and the Markov structure of the
  topology.
* `covariance_sfsLength_eq_four_mul_fuSigma_of_fuTopologyCov`: `hσ` from the deterministic
  identity `fuTopologyCov n i j = 4 σ_{ij}`.
* `fuTopologyCov_eq_four_mul_fuSigma_of_le_four`: that identity for `n ≤ 4`, evaluated from the
  definitions (`n = 4` already meets all six cases of `fuSigma`); hence `hσ` holds
  unconditionally for `n ≤ 4`
  (`covariance_sfsLength_eq_four_mul_fuSigma_of_le_four`) and Fu's SFS covariance follows
  (`covariance_count_kingman_of_le_four`).

## What is not proved

The deterministic identity `fuTopologyCov n i j = 4 σ_{ij}` for general `n`. It needs the joint
law of block counts at two levels in closed form (the nested uniform-composition structure of
random joining) followed by Fu's summation to harmonic numbers in each of the six cases of
`fuSigma`. The general theorem therefore takes it as the hypothesis `hfu`.

## References

* Y.-X. Fu, *Statistical properties of segregating sites*, Theor. Popul. Biol. 48 (1995),
  172–197.
* J. F. C. Kingman, *The coalescent*, Stoch. Proc. Appl. 13 (1982), 235–248.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFuDerivation

open SiteFrequencySpectrum SFSCovariance SFSFuClosedForm

/-! ### Two-level expectations under random joining -/

/-- The expectation of `g` at step `a` times `h` at step `b` (`a ≤ b`) of random joining started
from `x`: by the Markov property, `joinStep^[a] (g · joinStep^[b - a] h) x`
(`exists_finset_randomJoining_pair`). -/
noncomputable def joinPair (a b : ℕ) (g h : List ℕ → ℝ) (x : List ℕ) : ℝ :=
  joinStep^[a] (fun y => g y * joinStep^[b - a] h y) x

private lemma joinStep_iterate_nil (j : ℕ) (g : List ℕ → ℝ) : (joinStep^[j] g) [] = g [] := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', joinStep]; simp [blockPairs, ih]

private lemma joinStep_iterate_succ_of_card {x : List ℕ} (hx : (blockPairs x.length).card = 0)
    (j : ℕ) (g : List ℕ → ℝ) : (joinStep^[j + 1] g) x = g [] := by
  rw [Function.iterate_succ_apply', joinStep]
  simp [hx, joinStep_iterate_nil]

private lemma randomJoining_cons {m : ℕ} {b : List ℕ} (hb : (blockPairs b.length).card ≠ 0)
    (b' : List ℕ) (rest : List (List ℕ)) :
    randomJoining (m + 1) b (b' :: rest) = if b' = b then
      (∑ p ∈ blockPairs b.length, randomJoining m (mergeBlocks b p.1 p.2) rest) /
        (blockPairs b.length).card else 0 := by
  rw [randomJoining]
  simp only [hb, ↓reduceIte]

/-- **Two-level Markov property of random joining.** The random-joining law has finite support,
and the expectation of `g` at step `a` times `h` at step `b` (`a ≤ b ≤ m`) is `joinPair`. -/
theorem exists_finset_randomJoining_pair (m : ℕ) (x : List ℕ) :
    ∃ F : Finset (List (List ℕ)), (∀ ps ∉ F, randomJoining m x ps = 0) ∧
      ∀ a b, a ≤ b → b ≤ m → ∀ g h : List ℕ → ℝ,
        ∑ ps ∈ F, randomJoining m x ps * (g (ps.getD a []) * h (ps.getD b [])) =
          joinPair a b g h x := by
  induction m generalizing x with
  | zero =>
    refine ⟨{[x]}, fun ps hps => ?_, fun a b hab hb g h => ?_⟩
    · rw [mem_singleton] at hps
      simp [randomJoining, hps]
    · obtain rfl : b = 0 := by omega
      obtain rfl : a = 0 := by omega
      simp [randomJoining, joinPair]
  | succ m ih =>
    by_cases hx : (blockPairs x.length).card = 0
    · refine ⟨{[x]}, fun ps hps => ?_, fun a b hab hb g h => ?_⟩
      · rw [mem_singleton] at hps
        simp [randomJoining, hx, hps]
      · rw [sum_singleton]
        simp only [randomJoining, hx, ↓reduceIte, one_mul, joinPair]
        rcases a with _ | a
        · rcases b with _ | b
          · simp
          · simp only [Function.iterate_zero, id, Nat.sub_zero, joinStep_iterate_succ_of_card hx]
            simp
        · obtain ⟨b, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
          simp [joinStep_iterate_succ_of_card hx, joinStep_iterate_nil]
    · choose F hF0 hF using fun p : ℕ × ℕ => ih (mergeBlocks x p.1 p.2)
      have hsupp : ∀ rest p, p ∈ blockPairs x.length → rest ∉ F p →
          randomJoining m (mergeBlocks x p.1 p.2) rest = 0 := fun rest p _ h => hF0 p rest h
      refine ⟨((blockPairs x.length).biUnion F).image (List.cons x), fun ps hps => ?_, ?_⟩
      · rcases ps with _ | ⟨b', rest⟩
        · simp [randomJoining, hx]
        · rw [randomJoining_cons hx]
          split_ifs with hb'
          · subst hb'
            rw [div_eq_zero_iff]
            left
            refine sum_eq_zero fun p hp => hF0 p rest fun hr => hps ?_
            exact mem_image.2 ⟨rest, mem_biUnion.2 ⟨p, hp, hr⟩, rfl⟩
          · rfl
      have key : ∀ G : List (List ℕ) → ℝ,
          ∑ ps ∈ ((blockPairs x.length).biUnion F).image (List.cons x),
              randomJoining (m + 1) x ps * G ps =
            (∑ p ∈ blockPairs x.length, ∑ rest ∈ F p,
              randomJoining m (mergeBlocks x p.1 p.2) rest * G (x :: rest)) /
              (blockPairs x.length).card := by
        intro G
        rw [sum_image fun _ _ _ _ h => List.cons_injective h]
        simp only [randomJoining_cons hx, ↓reduceIte, sum_div, sum_mul]
        rw [sum_comm]
        refine sum_congr rfl fun p hp => ?_
        rw [← sum_subset (subset_biUnion_of_mem F hp) fun rest _ hr => by
          rw [hsupp rest p hp hr, zero_div, zero_mul]]
        exact sum_congr rfl fun _ _ => div_mul_eq_mul_div _ _ _
      have hc : ((blockPairs x.length).card : ℝ) ≠ 0 := by exact_mod_cast hx
      intro a b hab hb g h
      rw [key]
      rcases a with _ | a
      · simp only [List.getD_cons_zero]
        rcases b with _ | b
        · have h1 : ∀ p, ∑ rest ∈ F p, randomJoining m (mergeBlocks x p.1 p.2) rest = 1 := by
            intro p
            simpa [joinPair] using hF p 0 0 le_rfl (Nat.zero_le _) (fun _ => 1) (fun _ => 1)
          simp only [List.getD_cons_zero, ← sum_mul, h1, sum_const, nsmul_eq_mul, mul_one,
            joinPair, Function.iterate_zero, id, Nat.sub_zero]
          field_simp
        · simp only [List.getD_cons_succ]
          have hp : ∀ p, ∑ rest ∈ F p, randomJoining m (mergeBlocks x p.1 p.2) rest *
              (g x * h (rest.getD b [])) = g x * (joinStep^[b] h) (mergeBlocks x p.1 p.2) := by
            intro p
            have := hF p 0 b (Nat.zero_le _) (by omega) (fun _ => 1) h
            simp only [one_mul, joinPair, Function.iterate_zero, id, Nat.sub_zero] at this
            rw [← this, mul_sum]
            exact sum_congr rfl fun _ _ => by ring
          rw [sum_congr rfl fun p _ => hp p, ← mul_sum]
          simp only [joinPair, Function.iterate_zero, id, Nat.sub_zero,
            Function.iterate_succ_apply' joinStep b h, joinStep, hx, ↓reduceIte]
          ring
      · obtain ⟨b, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
        simp only [List.getD_cons_succ]
        rw [sum_congr rfl fun p _ => hF p a b (by omega) (by omega) g h]
        simp only [joinPair, Nat.add_sub_add_right, Function.iterate_succ_apply', joinStep, hx,
          ↓reduceIte]

/-! ### Moments of the block counts and of the holding times -/

/-- `E[c_{k,i}]`: the expected number of blocks of size `i` while `k` lineages remain, under
random joining started from `n` singletons (step `n - k`). -/
noncomputable def blockCountMean (n k i : ℕ) : ℝ :=
  joinStep^[n - k] (fun b => (b.count i : ℝ)) (List.replicate n 1)

/-- `E[c_{k,i} c_{l,j}]`: the joint second moment of the numbers of blocks of size `i` while `k`
lineages remain and of size `j` while `l` lineages remain, from the two-level Markov property
(the earlier step `n - max k l` comes first). -/
noncomputable def blockCountMoment (n k l i j : ℕ) : ℝ :=
  if l ≤ k then
    joinPair (n - k) (n - l) (fun b => (b.count i : ℝ)) (fun b => (b.count j : ℝ))
      (List.replicate n 1)
  else
    joinPair (n - l) (n - k) (fun b => (b.count j : ℝ)) (fun b => (b.count i : ℝ))
      (List.replicate n 1)

/-- `E[T_k T_l]` for independent `T_k ~ Exp(C(k, 2))`: `2 / C(k, 2)²` if `k = l`, else
`1 / (C(k, 2) C(l, 2))`. -/
noncomputable def kingmanTimeMoment (k l : ℕ) : ℝ :=
  if k = l then 2 * (((k.choose 2 : ℕ) : ℝ)⁻¹) ^ 2
  else ((k.choose 2 : ℕ) : ℝ)⁻¹ * ((l.choose 2 : ℕ) : ℝ)⁻¹

/-- The covariance of `L_i` and `L_j` in terms of the moments of the block counts and of the
holding times: `∑_{k,l} E[c_{k,i} c_{l,j}] E[T_k T_l] - E[L_i] E[L_j]`, with
`E[L_i] = ∑_k E[c_{k,i}] / C(k, 2)`. A deterministic number. -/
noncomputable def fuTopologyCov (n i j : ℕ) : ℝ :=
  ∑ k ∈ Icc 2 n, ∑ l ∈ Icc 2 n, blockCountMoment n k l i j * kingmanTimeMoment k l -
    (∑ k ∈ Icc 2 n, blockCountMean n k i * ((k.choose 2 : ℕ) : ℝ)⁻¹) *
      ∑ l ∈ Icc 2 n, blockCountMean n l j * ((l.choose 2 : ℕ) : ℝ)⁻¹

/-! ### Kingman's coalescent -/

section Kingman

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : ℕ}

private lemma integral_comp_randomJoining [IsProbabilityMeasure μ] {m : ℕ}
    {b : List ℕ} {τ : Ω → List (List ℕ)} (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining m b ps) {F : Finset (List (List ℕ))}
    (hF : ∀ ps ∉ F, randomJoining m b ps = 0) (g : List (List ℕ) → ℝ) :
    Integrable (fun ω => g (τ ω)) μ ∧
      μ[fun ω => g (τ ω)] = ∑ ps ∈ F, randomJoining m b ps * g ps := by
  have hmeas : ∀ ps, MeasurableSet (τ ⁻¹' {ps}) := fun ps =>
    hτ _ (MeasurableSpace.measurableSet_comap.2 ⟨{ps}, trivial, rfl⟩)
  have hae : ∀ᵐ ω ∂μ, τ ω ∈ F := by
    rw [ae_iff]
    have : {ω | ¬ τ ω ∈ F} = ⋃ ps : {ps // ps ∉ F}, τ ⁻¹' {ps.1} := by
      ext ω; simp
    rw [this]
    refine measure_iUnion_null fun ps => ?_
    rw [← measureReal_eq_zero_iff, hτ_law, hF _ ps.2]
  have heq : (fun ω => g (τ ω)) =ᵐ[μ]
      fun ω => ∑ ps ∈ F, (τ ⁻¹' {ps}).indicator (fun _ => g ps) ω := by
    filter_upwards [hae] with ω hω
    rw [Finset.sum_eq_single_of_mem (τ ω) hω]
    · simp
    · intro ps _ hne
      simp [Set.indicator, Ne.symm hne]
  have hint : ∀ ps ∈ F, Integrable ((τ ⁻¹' {ps}).indicator (fun _ => g ps)) μ :=
    fun ps _ => (integrable_const _).indicator (hmeas ps)
  refine ⟨(integrable_finsetSum _ hint).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun ps _ => ?_
  rw [integral_indicator_const _ (hmeas ps), hτ_law, smul_eq_mul]

private lemma memLp_T (K : KingmanTimes μ n) {k : ℕ} (hk : k ∈ Icc 2 n) : MemLp (K.T k) 2 μ :=
  (K.hasLaw k hk).memLp_comp (f := id)
    ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (by simpa using integrable_pow_expMeasure (KingmanTimes.choose_two_pos hk) 2))

/-- **Second moments of the Kingman holding times**: `E[T_k T_l] = kingmanTimeMoment k l` for
`2 ≤ k, l ≤ n` (exponential laws and independence). -/
theorem integral_T_mul_T [IsProbabilityMeasure μ] (K : KingmanTimes μ n) {k l : ℕ}
    (hk : k ∈ Icc 2 n) (hl : l ∈ Icc 2 n) :
    μ[K.T k * K.T l] = kingmanTimeMoment k l := by
  unfold kingmanTimeMoment
  split_ifs with hkl
  · subst hkl
    have hv := variance_eq_sub (memLp_T K hk)
    rw [(K.hasLaw k hk).variance_eq_of_expMeasure (KingmanTimes.choose_two_pos hk),
      K.integral_T hk] at hv
    rw [← pow_two]
    linarith
  · have hind : IndepFun (K.T k) (K.T l) μ :=
      K.indep.indepFun (i := ⟨k, hk⟩) (j := ⟨l, hl⟩) fun h => hkl (congrArg Subtype.val h)
    rw [hind.integral_mul_eq_mul_integral (K.integrable_T hk).aestronglyMeasurable
      (K.integrable_T hl).aestronglyMeasurable, K.integral_T hk, K.integral_T hl]

variable [IsProbabilityMeasure μ] {K : KingmanTimes μ n} {τ : Ω → List (List ℕ)}

omit [IsProbabilityMeasure μ] in
/-- A statistic of the topology is independent of a statistic of the holding times. -/
private lemma indepFun_topology_times
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (f : List (List ℕ) → ℝ) {G : (ℕ → ℝ) → ℝ} (hG : Measurable G) :
    IndepFun (fun ω => f (τ ω)) (fun ω => G (fun k => K.T k ω)) μ := by
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h_indep ?_) ?_
  · rw [show (fun ω => f (τ ω)) = f ∘ τ from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono le_top
  · rw [show (fun ω => G (fun k => K.T k ω)) = G ∘ (fun ω k => K.T k ω) from rfl,
      ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hG.comap_le

/-- **The covariances of the branch-length classes reduce to the topology.** Under Kingman's
coalescent (holding times `K.T`) with an independent block-size history `τ` with the
random-joining law, `Cov(L_i, L_j) = fuTopologyCov n i j` for all `i, j`, where
`L_i = sfsLength n i τ T`. -/
theorem covariance_sfsLength_eq_fuTopologyCov
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (i j : ℕ) :
    cov[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω),
      fun ω => sfsLength n j (τ ω) (fun k => K.T k ω); μ] = fuTopologyCov n i j := by
  obtain ⟨F, hF0, hF⟩ := exists_finset_randomJoining_pair (n - 1) (List.replicate n 1)
  set C : ℕ → ℝ := fun k => ((k.choose 2 : ℕ) : ℝ)⁻¹ with hC
  set c : ℕ → ℕ → List (List ℕ) → ℝ := fun k i ps => ((ps.getD (n - k) []).count i : ℝ)
    with hc
  -- the means
  have hmean : ∀ i, ∀ k ∈ Icc 2 n,
      Integrable (fun ω => c k i (τ ω) * K.T k ω) μ ∧
        μ[fun ω => c k i (τ ω) * K.T k ω] = blockCountMean n k i * C k := by
    intro i k hk
    have hk' := mem_Icc.1 hk
    obtain ⟨hXi, hXe⟩ := integral_comp_randomJoining hτ hτ_law hF0 (c k i)
    have hind : IndepFun (fun ω => c k i (τ ω)) (fun ω => K.T k ω) μ :=
      indepFun_topology_times h_indep (c k i) (measurable_pi_apply k)
    refine ⟨hind.integrable_mul hXi (K.integrable_T hk), ?_⟩
    change μ[(fun ω => c k i (τ ω)) * (fun ω => K.T k ω)] = _
    rw [hind.integral_mul_eq_mul_integral hXi.aestronglyMeasurable
      (K.integrable_T hk).aestronglyMeasurable, hXe, K.integral_T hk]
    have := hF 0 (n - k) (Nat.zero_le _) (by omega) (fun _ => 1) (fun b => (b.count i : ℝ))
    simp only [one_mul, joinPair, Function.iterate_zero, id, Nat.sub_zero] at this
    rw [this, blockCountMean]
  have hL : ∀ i, μ[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω)] =
      ∑ k ∈ Icc 2 n, blockCountMean n k i * C k := by
    intro i
    unfold sfsLength
    rw [integral_finsetSum _ fun k hk => (hmean i k hk).1]
    exact sum_congr rfl fun k hk => (hmean i k hk).2
  -- the cross moments
  have hterm : ∀ k ∈ Icc 2 n, ∀ l ∈ Icc 2 n,
      Integrable (fun ω => c k i (τ ω) * c l j (τ ω) * (K.T k ω * K.T l ω)) μ ∧
        μ[fun ω => c k i (τ ω) * c l j (τ ω) * (K.T k ω * K.T l ω)] =
          blockCountMoment n k l i j * kingmanTimeMoment k l := by
    intro k hk l hl
    obtain ⟨hXi, hXe⟩ := integral_comp_randomJoining hτ hτ_law hF0
      (fun ps => c k i ps * c l j ps)
    have hind : IndepFun (fun ω => c k i (τ ω) * c l j (τ ω)) (fun ω => K.T k ω * K.T l ω) μ :=
      indepFun_topology_times h_indep (fun ps => c k i ps * c l j ps)
        ((measurable_pi_apply k).mul (measurable_pi_apply l))
    have hYi : Integrable (K.T k * K.T l) μ := (memLp_T K hk).integrable_mul (memLp_T K hl)
    refine ⟨hind.integrable_mul hXi hYi, ?_⟩
    change μ[(fun ω => c k i (τ ω) * c l j (τ ω)) * (fun ω => K.T k ω * K.T l ω)] = _
    rw [hind.integral_mul_eq_mul_integral hXi.aestronglyMeasurable hYi.aestronglyMeasurable,
      hXe]
    change _ * μ[K.T k * K.T l] = _
    rw [integral_T_mul_T K hk hl, blockCountMoment]
    congr 1
    have hk' := mem_Icc.1 hk
    have hl' := mem_Icc.1 hl
    split_ifs with hlk
    · exact hF (n - k) (n - l) (by omega) (by omega) (fun b => (b.count i : ℝ))
        (fun b => (b.count j : ℝ))
    · rw [← hF (n - l) (n - k) (by omega) (by omega) (fun b => (b.count j : ℝ))
        (fun b => (b.count i : ℝ))]
      exact sum_congr rfl fun _ _ => by simp only [hc]; ring
  have hprod : (fun ω => sfsLength n i (τ ω) (fun k => K.T k ω)) *
      (fun ω => sfsLength n j (τ ω) (fun k => K.T k ω)) =
      fun ω => ∑ k ∈ Icc 2 n, ∑ l ∈ Icc 2 n,
        c k i (τ ω) * c l j (τ ω) * (K.T k ω * K.T l ω) := by
    funext ω
    simp only [Pi.mul_apply, sfsLength, sum_mul_sum, hc]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  rw [covariance_eq_sub (memLp_sfsLength hτ hτ_law i) (memLp_sfsLength hτ hτ_law j), hprod,
    integral_finsetSum _ fun k hk => integrable_finsetSum _ fun l hl => (hterm k hk l hl).1,
    sum_congr rfl fun k hk => integral_finsetSum _ fun l hl => (hterm k hk l hl).1, hL, hL,
    fuTopologyCov]
  exact congrArg (· - _) (sum_congr rfl fun k hk => sum_congr rfl fun l hl => (hterm k hk l hl).2)

/-- **`hσ` from the topology identity**: if `fuTopologyCov n i j = 4 σ_{ij}` for
`1 ≤ i, j ≤ n - 1`, then `Cov(L_i, L_j) = 4 σ_{ij}`, the hypothesis `hσ` of the theorems of
`SFSFuClosedForm`. -/
theorem covariance_sfsLength_eq_four_mul_fuSigma_of_fuTopologyCov
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (hfu : ∀ i ∈ Ico 1 n, ∀ j ∈ Ico 1 n, fuTopologyCov n i j = 4 * fuSigma n i j) :
    ∀ i ∈ Ico 1 n, ∀ j ∈ Ico 1 n,
      cov[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω),
        fun ω => sfsLength n j (τ ω) (fun k => K.T k ω); μ] = 4 * fuSigma n i j :=
  fun i hi j hj => by
    rw [covariance_sfsLength_eq_fuTopologyCov hτ hτ_law h_indep, hfu i hi j hj]

end Kingman

/-! ### Small samples -/

section Small

private lemma joinStep_nil (g : List ℕ → ℝ) : joinStep g [] = g [] := by
  simp [joinStep, blockPairs]

private lemma joinStep_singleton (g : List ℕ → ℝ) (a : ℕ) : joinStep g [a] = g [] := by
  simp [joinStep, blockPairs]

private lemma joinStep_pair (g : List ℕ → ℝ) (a b : ℕ) : joinStep g [a, b] = g [a + b] := by
  have : blockPairs 2 = {(0, 1)} := by decide
  simp [joinStep, this, mergeBlocks]

private lemma joinStep_111 (g : List ℕ → ℝ) : joinStep g [1, 1, 1] = g [1, 2] := by
  have : blockPairs 3 = {(0, 1), (0, 2), (1, 2)} := by decide
  simp [joinStep, this, mergeBlocks]
  ring

private lemma joinStep_112 (g : List ℕ → ℝ) :
    joinStep g [1, 1, 2] = (g [2, 2] + 2 * g [1, 3]) / 3 := by
  have : blockPairs 3 = {(0, 1), (0, 2), (1, 2)} := by decide
  simp [joinStep, this, mergeBlocks]
  ring

private lemma joinStep_1111 (g : List ℕ → ℝ) : joinStep g [1, 1, 1, 1] = g [1, 1, 2] := by
  have : blockPairs 4 = {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by decide
  simp [joinStep, this, mergeBlocks]
  ring

/-- **The topology identity for small samples**: `fuTopologyCov n i j = 4 σ_{ij}` for `n ≤ 4`,
evaluated from the definitions of `randomJoining`'s transition operator and of `fuSigma`. -/
theorem fuTopologyCov_eq_four_mul_fuSigma_of_le_four {n : ℕ} (hn : n ≤ 4) :
    ∀ i ∈ Ico 1 n, ∀ j ∈ Ico 1 n, fuTopologyCov n i j = 4 * fuSigma n i j := by
  intro i hi j hj
  obtain ⟨hi1, hi2⟩ := mem_Ico.1 hi
  obtain ⟨hj1, hj2⟩ := mem_Ico.1 hj
  interval_cases n <;> interval_cases i <;> interval_cases j <;>
    norm_num [fuTopologyCov, blockCountMoment, blockCountMean, joinPair, kingmanTimeMoment,
      fuSigma, fuBeta, tajimaA1, sum_Ico_succ_top, Nat.choose, Function.iterate_succ_apply',
      joinStep_nil, joinStep_singleton, joinStep_pair, joinStep_111, joinStep_112,
      joinStep_1111, show Icc 2 2 = {2} by decide, show Icc 2 3 = {2, 3} by decide,
      show Icc 2 4 = {2, 3, 4} by decide]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
  {K : KingmanTimes μ n} {τ : Ω → List (List ℕ)}

/-- **Fu's branch-length covariances for `n ≤ 4`**, unconditionally: under Kingman's coalescent
with an independent random-joining topology, `Cov(L_i, L_j) = 4 σ_{ij}` for
`1 ≤ i, j ≤ n - 1`. -/
theorem covariance_sfsLength_eq_four_mul_fuSigma_of_le_four (hn : n ≤ 4)
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ) :
    ∀ i ∈ Ico 1 n, ∀ j ∈ Ico 1 n,
      cov[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω),
        fun ω => sfsLength n j (τ ω) (fun k => K.T k ω); μ] = 4 * fuSigma n i j :=
  covariance_sfsLength_eq_four_mul_fuSigma_of_fuTopologyCov hτ hτ_law h_indep
    (fuTopologyCov_eq_four_mul_fuSigma_of_le_four hn)

/-- **Fu's SFS covariance for `n ≤ 4`** (Fu 1995), without the hypothesis `hσ`:
`Cov(ξ_i, ξ_j) = δ_{ij} θ / i + σ_{ij} θ²` for `1 ≤ i, j ≤ n - 1`. -/
theorem covariance_count_kingman_of_le_four (hn : n ≤ 4) (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    {θ : ℝ} {ξ : ℕ → Ω → ℝ}
    (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω)))
    {i j : ℕ} (hi : i ∈ Ico 1 n) (hj : j ∈ Ico 1 n) :
    cov[ξ i, ξ j; μ] = (if i = j then θ / i else 0) + θ ^ 2 * fuSigma n i j :=
  covariance_count_kingman_of_fuSigma hT hτ hτ_law h_indep h
    (covariance_sfsLength_eq_four_mul_fuSigma_of_le_four hn hτ hτ_law h_indep) hi hj

end Small

end MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFuDerivation
