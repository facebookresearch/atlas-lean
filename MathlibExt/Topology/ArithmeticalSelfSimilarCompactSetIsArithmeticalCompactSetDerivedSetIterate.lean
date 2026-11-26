/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.ArithmeticalSelfSimilarCompactSet
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Iterate
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Derived sets of arithmetical compact sets

The `n`-th derived set of an arithmetical compact set is arithmetical.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 7.
-/

namespace MetaMathlibExt

open Ordinal Filter Topology
open scoped Pointwise

namespace isArithmeticalCompactSet_derivedSet_iterate

private theorem image_derivedSet {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsClosedEmbedding f) (s : Set X) :
    derivedSet (f '' s) = f '' derivedSet s := by
  apply Set.Subset.antisymm _ (hf.continuous.image_derivedSet hf.injective)
  intro y hy
  have hy_range : y ∈ Set.range f :=
    hf.isClosed_range.closure_subset
      (closure_mono (Set.image_subset_range f s) (derivedSet_subset_closure _ hy))
  obtain ⟨x, rfl⟩ := hy_range
  refine ⟨x, ?_, rfl⟩
  simp only [mem_derivedSet, accPt_principal_iff_clusterPt, ← mem_closure_iff_clusterPt] at hy ⊢
  rwa [← Set.image_singleton, ← Set.image_sdiff hf.injective, hf.closure_image_eq,
    hf.injective.mem_set_image] at hy

private theorem derivedSet_smul {c : ℝ} (hc : c ≠ 0) (A : Set ℝ) :
    derivedSet (c • A) = c • derivedSet A := by
  let e := Homeomorph.mulLeft₀ c hc
  have h := image_derivedSet e.isClosedEmbedding A
  change derivedSet (e '' A) = e '' derivedSet A at h ⊢
  exact h

private theorem smul_iterate {c : ℝ} (hc : c ≠ 0) (A : Set ℝ) (m : ℕ) :
    c • derivedSet^[m] A = derivedSet^[m] (c • A) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← derivedSet_smul hc, ih]

private theorem smul_mem {c : ℝ} (hc : c ≠ 0) {A : Set ℝ} {x : ℝ} :
    x ∈ c • A ↔ x / c ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_eq_mul, mul_div_cancel_left₀ _ hc] using hy
  · intro hx
    refine ⟨x / c, hx, ?_⟩
    simp only [smul_eq_mul]
    rw [mul_comm]
    exact div_mul_cancel₀ _ hc

private theorem isClosed_of_isSelfSimilar {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) : IsClosed K :=
  hK.2.2.1.isClosed

private theorem antitone_iterate {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) :
    Antitone fun m => derivedSet^[m] K := by
  apply Monotone.antitone_iterate_of_map_le (fun _ _ h => derivedSet_mono _ _ h)
  exact (isClosed_iff_derivedSet_subset K).mp (isClosed_of_isSelfSimilar hK)

private theorem isCompact_iterate {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) (m : ℕ) :
    IsCompact (derivedSet^[m] K) := by
  induction m with
  | zero => exact hK.2.2.1
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact ih.of_isClosed_subset (isClosed_derivedSet _)
      ((isClosed_iff_derivedSet_subset _).mp ih.isClosed)

private theorem subset_iterate {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) (m : ℕ) :
    derivedSet^[m] K ⊆ K := by
  simpa using antitone_iterate hK (Nat.zero_le m)

private theorem scalar_pos {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsQuasiArithmeticalCompactSet K μ ρ) : (1 : ℝ) < ρ := by
  have h2 : 2 ≤ ρ := hK.1
  exact_mod_cast (by omega : 1 < ρ)

private theorem scalar_ne_zero {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsQuasiArithmeticalCompactSet K μ ρ) : (ρ : ℝ) ≠ 0 :=
  (zero_lt_one.trans (scalar_pos hK)).ne'

private theorem not_dvd_one {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsQuasiArithmeticalCompactSet K μ ρ) : ¬ ρ ∣ 1 := by
  intro h
  have h2 : 2 ≤ ρ := hK.1
  have hle := Nat.le_of_dvd (by norm_num) h
  omega

private theorem mem_of_mem_diff {K : Set ℝ} {ρ : ℕ} {κ : ℕ → ℕ}
    (hκ : K \ {0} = {x | ∃ n k : ℕ, ¬ ρ ∣ n ∧ κ n ≤ k ∧ x = n / (ρ : ℝ) ^ k})
    {n k : ℕ} (hn : ¬ ρ ∣ n) (hk : κ n ≤ k) :
    (n : ℝ) / (ρ : ℝ) ^ k ∈ K \ {0} := by
  rw [hκ]
  exact ⟨n, k, hn, hk, rfl⟩

private theorem module_pos {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsQuasiArithmeticalCompactSet K μ ρ) : 0 < μ := by
  by_contra h
  have hμ : μ = 0 := Nat.eq_zero_of_not_pos h
  subst hμ
  have hS := hK.isSelfSimilarCompactSet
  obtain ⟨κ, hκ⟩ := hK.2.2
  have hρ0 := scalar_ne_zero hK
  have hx0 : (1 : ℝ) / (ρ : ℝ) ^ κ 1 ∈ K := by
    simpa using (mem_of_mem_diff hκ (not_dvd_one hK) le_rfl).1
  have hx0pos : (0 : ℝ) < 1 / (ρ : ℝ) ^ κ 1 := by positivity
  have heq : (ρ : ℝ) • K = K := by
    simpa using hS.smul_derivedSet_iterate
  have hmem : ∀ j : ℕ, (1 / (ρ : ℝ) ^ κ 1) * (ρ : ℝ) ^ j ∈ K := by
    intro j
    induction j with
    | zero => simpa using hx0
    | succ j ih =>
      have hmul : (1 / (ρ : ℝ) ^ κ 1) * (ρ : ℝ) ^ (j + 1)
          = (ρ : ℝ) * ((1 / (ρ : ℝ) ^ κ 1) * (ρ : ℝ) ^ j) := by ring
      rw [hmul, ← heq, smul_mem hρ0]
      simpa [mul_div_cancel_left₀ _ hρ0] using ih
  obtain ⟨M, hM⟩ := bddAbove_def.mp hS.2.2.1.bddAbove
  have hlim : Filter.Tendsto (fun j => (1 / (ρ : ℝ) ^ κ 1) * (ρ : ℝ) ^ j)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hx0pos
      (tendsto_pow_atTop_atTop_of_one_lt (scalar_pos hK))
  obtain ⟨j, hj⟩ := (hlim.eventually_ge_atTop (M + 1)).exists
  have hle := hM _ (hmem j)
  linarith

private theorem mem_layer_div {K : Set ℝ} {μ : ℕ} {ρ x : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) {v : ℕ} (hx : x ∈ selfSimilarLayer K v) :
    x / ρ ∈ selfSimilarLayer K (v + μ) := by
  have hρ : ρ ≠ 0 := (zero_lt_one.trans hK.1).ne'
  let e := Homeomorph.mulLeft₀ ρ hρ
  have comm : Function.Commute (Set.preimage e) derivedSet := by
    intro A
    ext y
    simp only [Set.mem_preimage, mem_derivedSet, ← Filter.comap_principal,
      e.isOpenEmbedding.accPt_comap_iff]
  have he : e '' derivedSet^[μ] K = K := hK.smul_derivedSet_iterate
  have pre : e ⁻¹' K = derivedSet^[μ] K := by
    conv_lhs => rw [← he, e.preimage_image]
  have shift (i : ℕ) : e ⁻¹' derivedSet^[i] K = derivedSet^[i + μ] K := by
    rw [Function.iterate_add_apply, ← pre]
    exact comm.iterate_right i K
  have hlayer : e ⁻¹' selfSimilarLayer K v = selfSimilarLayer K (v + μ) := by
    simp only [selfSimilarLayer, Set.preimage_sdiff, shift, Nat.add_right_comm v 1 μ]
  rw [← hlayer]
  have hdiv : ρ * (x / ρ) = x := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hρ
  change ρ * (x / ρ) ∈ selfSimilarLayer K v
  rwa [hdiv]

private theorem mem_layer_div_pow {K : Set ℝ} {μ : ℕ} {ρ x : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) {v : ℕ} (hx : x ∈ selfSimilarLayer K v) (j : ℕ) :
    x / ρ ^ j ∈ selfSimilarLayer K (v + j * μ) := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    simpa [pow_succ, ← div_div, Nat.succ_mul, Nat.add_assoc] using mem_layer_div hK ih

private theorem layer_unique {K : Set ℝ} (hK : IsClosed K) {x : ℝ} {v w : ℕ}
    (hv : x ∈ selfSimilarLayer K v) (hw : x ∈ selfSimilarLayer K w) : v = w := by
  have hmono : Monotone (derivedSet : Set ℝ → Set ℝ) := fun _ _ => derivedSet_mono _ _
  have hanti := hmono.antitone_iterate_of_map_le ((isClosed_iff_derivedSet_subset K).mp hK)
  exact le_antisymm (le_of_not_gt fun h => hw.2 (hanti h hv.1))
    (le_of_not_gt fun h => hv.2 (hanti h hw.1))

private theorem layer_index_add {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) {n : ℝ} {p q v w : ℕ}
    (hv : n / ρ ^ p ∈ selfSimilarLayer K v)
    (hw : n / ρ ^ q ∈ selfSimilarLayer K w) :
    v + q * μ = w + p * μ := by
  have hv' := mem_layer_div_pow hK hv q
  have hw' := mem_layer_div_pow hK hw p
  rw [div_div, ← pow_add] at hv' hw'
  rw [Nat.add_comm q p] at hw'
  exact layer_unique (isClosed_of_isSelfSimilar hK) hv' hw'

private theorem layer_shift {K : Set ℝ} (j w : ℕ) :
    selfSimilarLayer (derivedSet^[j] K) w = selfSimilarLayer K (w + j) := by
  induction j generalizing w with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ← selfSimilarLayer_succ, ih]
    congr 1
    omega

private theorem iInter_subset_singleton {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsQuasiArithmeticalCompactSet K μ ρ) :
    ⋂ m, derivedSet^[m] K ⊆ {0} := by
  intro x hx
  rw [Set.mem_iInter] at hx
  rw [Set.mem_singleton_iff]
  have hS := hK.isSelfSimilarCompactSet
  have hρ0 : (ρ : ℝ) ≠ 0 := scalar_ne_zero hK
  have hmem : ∀ j m : ℕ, (ρ : ℝ) ^ j * x ∈ derivedSet^[m] K := by
    intro j
    induction j with
    | zero =>
      intro m
      simpa using hx m
    | succ j ih =>
      intro m
      have hmul : (ρ : ℝ) ^ (j + 1) * x = (ρ : ℝ) * ((ρ : ℝ) ^ j * x) := by ring
      rw [hmul]
      have h1 : (ρ : ℝ) ^ j * x ∈ derivedSet^[m] (derivedSet^[μ] K) := by
        have h := ih (m + μ)
        rwa [Function.iterate_add_apply] at h
      have h2 : (ρ : ℝ) * ((ρ : ℝ) ^ j * x)
          ∈ (ρ : ℝ) • derivedSet^[m] (derivedSet^[μ] K) := by
        rw [smul_mem hρ0]
        simpa [mul_div_cancel_left₀ _ hρ0] using h1
      rw [smul_iterate hρ0 _ m, hS.smul_derivedSet_iterate] at h2
      exact h2
  have hxK : x ∈ K := hx 0
  have hxnn : 0 ≤ x := hS.2.2.2.1 hxK
  by_contra hne
  have hxpos : 0 < x := lt_of_le_of_ne hxnn (Ne.symm hne)
  obtain ⟨M, hM⟩ := bddAbove_def.mp hS.2.2.1.bddAbove
  have hlim : Filter.Tendsto (fun j => (ρ : ℝ) ^ j * x) Filter.atTop Filter.atTop := by
    have h := Filter.Tendsto.const_mul_atTop hxpos
      (tendsto_pow_atTop_atTop_of_one_lt (scalar_pos hK))
    simpa [mul_comm] using h
  obtain ⟨j, hj⟩ := (hlim.eventually_ge_atTop (M + 1)).exists
  have hKj : (ρ : ℝ) ^ j * x ∈ K := hmem j 0
  have hle := hM _ hKj
  linarith

private theorem exists_layer {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsQuasiArithmeticalCompactSet K μ ρ) {x : ℝ} (hx : x ∈ K) (hx0 : x ≠ 0) :
    ∃ u, x ∈ selfSimilarLayer K u := by
  have hne_mem : {m : ℕ | x ∉ derivedSet^[m] K}.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hxI : x ∈ ⋂ m, derivedSet^[m] K := by
      rw [Set.mem_iInter]
      intro m
      by_contra hm
      have hmem : m ∈ {m : ℕ | x ∉ derivedSet^[m] K} := hm
      rw [hcon] at hmem
      exact Set.notMem_empty m hmem
    have h0 := iInter_subset_singleton hK hxI
    rw [Set.mem_singleton_iff] at h0
    exact absurd h0 hx0
  set m₀ := sInf {m : ℕ | x ∉ derivedSet^[m] K} with hm₀
  have hm₀mem : m₀ ∈ {m : ℕ | x ∉ derivedSet^[m] K} := Nat.sInf_mem hne_mem
  have hm₀pos : 0 < m₀ := by
    by_contra hc
    have hzero : m₀ = 0 := by omega
    rw [hzero] at hm₀mem
    exact hm₀mem (by simpa using hx)
  obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hm₀pos)
  refine ⟨u, ?_, ?_⟩
  · by_contra hcon
    have hmem : u ∈ {m : ℕ | x ∉ derivedSet^[m] K} := hcon
    have hle := Nat.sInf_le hmem
    omega
  · simpa [hu] using hm₀mem

private theorem zero_mem_iterate {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsQuasiArithmeticalCompactSet K μ ρ) (m : ℕ) :
    0 ∈ derivedSet^[m] K := by
  have hS := hK.isSelfSimilarCompactSet
  obtain ⟨κ, hκ⟩ := hK.2.2
  have hρ0 : (ρ : ℝ) ≠ 0 := scalar_ne_zero hK
  have hρ1 : (1 : ℝ) < ρ := scalar_pos hK
  have hμpos : 0 < μ := module_pos hK
  have hmemK : ∀ k : ℕ, κ 1 ≤ k → ((1 : ℕ) : ℝ) / (ρ : ℝ) ^ k ∈ K := by
    intro k hk
    exact (mem_of_mem_diff hκ (not_dvd_one hK) hk).1
  have hneK : ∀ k : ℕ, ((1 : ℕ) : ℝ) / (ρ : ℝ) ^ k ≠ 0 := by
    intro k
    apply div_ne_zero (by norm_num)
    exact pow_ne_zero k hρ0
  have hlim : ∀ K₀ : ℕ, Filter.Tendsto (fun k => ((1 : ℕ) : ℝ) / (ρ : ℝ) ^ (K₀ + k))
      Filter.atTop (nhds 0) := by
    intro K₀
    have hr0 : (0 : ℝ) ≤ 1 / (ρ : ℝ) := by positivity
    have hr1 : (1 : ℝ) / (ρ : ℝ) < 1 := by
      rw [div_lt_one (zero_lt_one.trans hρ1)]
      exact hρ1
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have heq : (fun k => ((1 : ℕ) : ℝ) / (ρ : ℝ) ^ (K₀ + k))
        = (fun k => (1 / (ρ : ℝ)) ^ K₀ * (1 / (ρ : ℝ)) ^ k) := by
      funext k
      rw [← pow_add, div_pow, one_pow, Nat.cast_one]
    rw [heq]
    have hmul := Filter.Tendsto.const_mul ((1 / (ρ : ℝ)) ^ K₀) hpow
    simpa using hmul
  cases m with
  | zero =>
    have h0 : (0 : ℝ) ∈ K :=
      hS.2.2.1.isClosed.mem_of_tendsto (hlim (κ 1))
        (Filter.Eventually.of_forall fun k => hmemK _ (by omega : κ 1 ≤ κ 1 + k))
    simpa using h0
  | succ m =>
    rw [Function.iterate_succ_apply', mem_derivedSet, accPt_principal_iff_clusterPt,
      ← mem_closure_iff_clusterPt]
    apply mem_closure_of_tendsto (hlim (κ 1 + m))
    apply Filter.Eventually.of_forall
    intro k
    obtain ⟨u₀, hu₀⟩ := exists_layer hK (hmemK _ le_rfl) (hneK _)
    have hkκ : κ 1 ≤ κ 1 + m + k := by omega
    obtain ⟨u₁, hu₁⟩ := exists_layer hK (hmemK _ hkκ) (hneK _)
    have hcore := layer_index_add hS hu₀ hu₁
    rw [add_mul, add_mul] at hcore
    have hle : m ≤ m * μ := Nat.le_mul_of_pos_right _ hμpos
    have hum : m ≤ u₁ := by omega
    refine ⟨?_, ?_⟩
    · exact (antitone_iterate hS hum) hu₁.1
    · rw [Set.mem_singleton_iff]
      exact hneK _

private theorem reduce_fraction {ρ : ℕ} (hρ : 2 ≤ ρ) {m : ℕ} (hm : 0 < m) :
    ∃ n' v : ℕ, ¬ ρ ∣ n' ∧ 0 < n' ∧
      ∀ ℓ : ℕ, v ≤ ℓ → (m : ℝ) / (ρ : ℝ) ^ ℓ = (n' : ℝ) / (ρ : ℝ) ^ (ℓ - v) := by
  have hρ0 : (ρ : ℝ) ≠ 0 := by exact_mod_cast (by omega : ρ ≠ 0)
  have hexp : ∃ v : ℕ, ¬ ρ ^ (v + 1) ∣ m := by
    refine ⟨m, ?_⟩
    intro hdiv
    have hle := Nat.le_of_dvd hm hdiv
    have hlt : m < ρ ^ (m + 1) := by
      calc m < 2 ^ (m + 1) := by
            have h := Nat.lt_two_pow_self (n := m + 1)
            omega
        _ ≤ ρ ^ (m + 1) := Nat.pow_le_pow_left hρ _
    omega
  set v := sInf {v : ℕ | ¬ ρ ^ (v + 1) ∣ m} with hv
  have hvmem : v ∈ {v : ℕ | ¬ ρ ^ (v + 1) ∣ m} := Nat.sInf_mem hexp
  have hvdvd : ρ ^ v ∣ m := by
    by_contra hcon
    have hvpos : 0 < v := by
      by_contra hc
      have hzero : v = 0 := by omega
      rw [hzero] at hcon
      simp at hcon
    obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hvpos)
    have hvv : v = u + 1 := by omega
    have hunmem : u ∉ {v : ℕ | ¬ ρ ^ (v + 1) ∣ m} := by
      intro hmem
      have hle := Nat.sInf_le hmem
      omega
    simp only [Set.mem_ofPred_eq, not_not] at hunmem
    have hdiv : ρ ^ v ∣ m := by
      rw [hvv]
      exact hunmem
    exact hcon hdiv
  set n' := m / ρ ^ v with hn'
  have hmul : ρ ^ v * n' = m := by
    rw [hn', mul_comm]
    exact Nat.div_mul_cancel hvdvd
  have hn'pos : 0 < n' := by
    by_contra hc
    have hzero : n' = 0 := Nat.eq_zero_of_not_pos hc
    rw [hzero, mul_zero] at hmul
    omega
  have hn'dvd : ¬ ρ ∣ n' := by
    intro hdiv
    have h1 : ρ * ρ ^ v ∣ n' * ρ ^ v := mul_dvd_mul hdiv (dvd_refl _)
    rw [mul_comm n' (ρ ^ v)] at h1
    have h2 : ρ ^ (v + 1) = ρ * ρ ^ v := by ring
    rw [← h2, hmul] at h1
    exact hvmem h1
  refine ⟨n', v, hn'dvd, hn'pos, ?_⟩
  intro ℓ hℓ
  have hρℓ : (ρ : ℝ) ^ ℓ = (ρ : ℝ) ^ v * (ρ : ℝ) ^ (ℓ - v) := by
    rw [← pow_add, Nat.add_sub_cancel' hℓ]
  have hmcast : (m : ℝ) = (ρ : ℝ) ^ v * (n' : ℝ) := by
    exact_mod_cast hmul.symm
  rw [hmcast, hρℓ, mul_div_mul_left _ _ (pow_ne_zero _ hρ0)]

private theorem gaugeIndex_eq {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsQuasiArithmeticalCompactSet K μ ρ) (j : ℕ) {m : ℕ} (hm : 0 < m) :
    stabilityGaugeIndex (derivedSet^[j] K) μ ρ m
      = stabilityGaugeIndex K μ ρ m + j := by
  have hS := hK.isSelfSimilarCompactSet
  obtain ⟨κ, hκ⟩ := hK.2.2
  obtain ⟨n', v, hn'dvd, hn'pos, hred⟩ := reduce_fraction hK.1 hm
  have hmemK : ∀ ℓ : ℕ, v + κ n' ≤ ℓ → (m : ℝ) / (ρ : ℝ) ^ ℓ ∈ K := by
    intro ℓ hℓ
    have h1 : (m : ℝ) / (ρ : ℝ) ^ ℓ = (n' : ℝ) / (ρ : ℝ) ^ (ℓ - v) :=
      hred ℓ (by omega)
    have h2 : ((n' : ℕ) : ℝ) / (ρ : ℝ) ^ (ℓ - v) ∈ K :=
      (mem_of_mem_diff hκ hn'dvd (by omega : κ n' ≤ ℓ - v)).1
    rw [h1]
    exact h2
  have hneK : ∀ ℓ : ℕ, (m : ℝ) / (ρ : ℝ) ^ ℓ ≠ 0 := by
    intro ℓ
    apply div_ne_zero _ (pow_ne_zero ℓ (scalar_ne_zero hK))
    exact_mod_cast (ne_of_gt hm)
  have hneKwit : {ℓ : ℕ | ∃ u, (m : ℝ) / (ρ : ℝ) ^ ℓ ∈ selfSimilarLayer K u}.Nonempty := by
    refine ⟨v + κ n', ?_⟩
    exact exists_layer hK (hmemK _ le_rfl) (hneK _)
  have hneK'wit : {ℓ : ℕ |
      ∃ u, (m : ℝ) / (ρ : ℝ) ^ ℓ ∈ selfSimilarLayer (derivedSet^[j] K) u}.Nonempty := by
    have hmem0 : (m : ℝ) / (ρ : ℝ) ^ (v + κ n') ∈ K := hmemK _ le_rfl
    obtain ⟨U₀, hU₀⟩ := exists_layer hK hmem0 (hneK _)
    have hmem1 : (m : ℝ) / (ρ : ℝ) ^ (v + κ n' + j) ∈ K := hmemK _ (by omega)
    obtain ⟨Ustar, hUstar⟩ := exists_layer hK hmem1 (hneK _)
    have he0 : (v + κ n') - v = κ n' := by omega
    have hr0 : (m : ℝ) / (ρ : ℝ) ^ (v + κ n') = (n' : ℝ) / (ρ : ℝ) ^ κ n' := by
      have h := hred (v + κ n') (by omega : v ≤ v + κ n')
      rw [he0] at h
      exact h
    have he1 : (v + κ n' + j) - v = κ n' + j := by omega
    have hr1 : (m : ℝ) / (ρ : ℝ) ^ (v + κ n' + j)
        = (n' : ℝ) / (ρ : ℝ) ^ (κ n' + j) := by
      have h := hred (v + κ n' + j) (by omega : v ≤ v + κ n' + j)
      rw [he1] at h
      exact h
    rw [hr0] at hU₀
    rw [hr1] at hUstar
    have hcore := layer_index_add hS hU₀ hUstar
    rw [add_mul] at hcore
    have hle : j ≤ j * μ := Nat.le_mul_of_pos_right _ (module_pos hK)
    have hum : j ≤ Ustar := by omega
    refine ⟨v + κ n' + j, Ustar - j, ?_⟩
    rw [← hr1] at hUstar
    have hUeq : Ustar = (Ustar - j) + j := (Nat.sub_add_cancel hum).symm
    rw [hUeq, ← layer_shift j (Ustar - j)] at hUstar
    exact hUstar
  set ℓ := sInf {ℓ : ℕ | ∃ u, (m : ℝ) / (ρ : ℝ) ^ ℓ ∈ selfSimilarLayer K u} with hℓ
  have hℓmem : ∃ u, (m : ℝ) / (ρ : ℝ) ^ ℓ ∈ selfSimilarLayer K u :=
    Nat.sInf_mem hneKwit
  obtain ⟨u, hu⟩ := hℓmem
  set uS := sInf {u : ℕ | (m : ℝ) / (ρ : ℝ) ^ ℓ ∈ selfSimilarLayer K u} with huS
  have huSmem : uS ∈ {u : ℕ | (m : ℝ) / (ρ : ℝ) ^ ℓ ∈ selfSimilarLayer K u} :=
    Nat.sInf_mem ⟨u, hu⟩
  set ℓ' := sInf {ℓ : ℕ |
    ∃ u, (m : ℝ) / (ρ : ℝ) ^ ℓ ∈ selfSimilarLayer (derivedSet^[j] K) u} with hℓ'
  have hℓ'mem : ∃ u, (m : ℝ) / (ρ : ℝ) ^ ℓ'
      ∈ selfSimilarLayer (derivedSet^[j] K) u :=
    Nat.sInf_mem hneK'wit
  obtain ⟨u', hu'⟩ := hℓ'mem
  set uS' := sInf {u : ℕ |
    (m : ℝ) / (ρ : ℝ) ^ ℓ' ∈ selfSimilarLayer (derivedSet^[j] K) u} with huS'
  have huS'mem : uS' ∈ {u : ℕ |
      (m : ℝ) / (ρ : ℝ) ^ ℓ' ∈ selfSimilarLayer (derivedSet^[j] K) u} :=
    Nat.sInf_mem ⟨u', hu'⟩
  have hvK : (m : ℝ) / (ρ : ℝ) ^ ℓ ∈ selfSimilarLayer K uS := huSmem
  have hvK' : (m : ℝ) / (ρ : ℝ) ^ ℓ' ∈ selfSimilarLayer (derivedSet^[j] K) uS' :=
    huS'mem
  have hUmem : (m : ℝ) / (ρ : ℝ) ^ ℓ' ∈ selfSimilarLayer K (uS' + j) := by
    rw [layer_shift j uS'] at hvK'
    exact hvK'
  have hcore := layer_index_add hS hvK hUmem
  have hgK : stabilityGaugeIndex K μ ρ m = ((ℓ * μ : ℕ) : ℤ) - (uS : ℤ) := rfl
  have hgK' : stabilityGaugeIndex (derivedSet^[j] K) μ ρ m
      = ((ℓ' * μ : ℕ) : ℤ) - (uS' : ℤ) := rfl
  rw [hgK, hgK']
  set A := ℓ' * μ with hA
  set B := ℓ * μ with hB
  omega

private theorem gauge_eq {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsQuasiArithmeticalCompactSet K μ ρ) (j : ℕ) {m : ℕ} (hm : 0 < m) :
    stabilityGauge (derivedSet^[j] K) μ ρ m = stabilityGauge K μ ρ m := by
  have h1 := gaugeIndex_eq hK j hm
  have h2 := gaugeIndex_eq hK j (by norm_num : 0 < 1)
  unfold stabilityGauge
  omega

private theorem selfSimilar_transfer {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsQuasiArithmeticalCompactSet K μ ρ) (j : ℕ) :
    IsSelfSimilarCompactSet (derivedSet^[j] K) μ (ρ : ℝ) := by
  have hS := hK.isSelfSimilarCompactSet
  have hρ0 : (ρ : ℝ) ≠ 0 := scalar_ne_zero hK
  refine ⟨scalar_pos hK, ⟨0, zero_mem_iterate hK j⟩, isCompact_iterate hS j, ?_, ?_, ?_⟩
  · exact (subset_iterate hS j).trans hS.2.2.2.1
  · exact hS.2.2.2.2.1.mono le_rfl (subset_iterate hS j)
  · have e1 : derivedSet^[μ + j] K = derivedSet^[μ] (derivedSet^[j] K) :=
      Function.iterate_add_apply _ _ _ _
    have e2 : derivedSet^[μ + j] K = derivedSet^[j] (derivedSet^[μ] K) := by
      rw [add_comm μ j]
      exact Function.iterate_add_apply _ _ _ _
    rw [← e1, e2, smul_iterate hρ0 _ j, hS.smul_derivedSet_iterate]

private theorem quasi_transfer {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsQuasiArithmeticalCompactSet K μ ρ) (j : ℕ) :
    IsQuasiArithmeticalCompactSet (derivedSet^[j] K) μ ρ := by
  have hS := hK.isSelfSimilarCompactSet
  obtain ⟨κ, hκ⟩ := hK.2.2
  refine ⟨hK.1, selfSimilar_transfer hK j, ?_⟩
  set κ' : ℕ → ℕ := fun n => sInf {k : ℕ | κ n ≤ k ∧
    ∃ u, j ≤ u ∧ (n : ℝ) / (ρ : ℝ) ^ k ∈ selfSimilarLayer K u} with hκ'
  refine ⟨κ', ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hxD, hx0⟩ := hx
    have hxK : x ∈ K := subset_iterate hS j hxD
    have hxK0 : x ∈ K \ {0} := ⟨hxK, hx0⟩
    rw [hκ] at hxK0
    have hxrep : ∃ n k : ℕ, ¬ ρ ∣ n ∧ κ n ≤ k ∧ x = (n : ℝ) / (ρ : ℝ) ^ k := hxK0
    obtain ⟨n, k, hndiv, hκn, rfl⟩ := hxrep
    have hxne : (n : ℝ) / (ρ : ℝ) ^ k ≠ 0 := by simpa using hx0
    obtain ⟨u, hu⟩ := exists_layer hK hxK hxne
    have huge : j ≤ u := by
      by_contra hcon
      have hsub : derivedSet^[j] K ⊆ derivedSet^[u + 1] K :=
        antitone_iterate hS (by omega : u + 1 ≤ j)
      exact hu.2 (hsub hxD)
    have hkmem : k ∈ {k : ℕ | κ n ≤ k ∧
        ∃ u, j ≤ u ∧ (n : ℝ) / (ρ : ℝ) ^ k ∈ selfSimilarLayer K u} :=
      ⟨hκn, u, huge, hu⟩
    have hle : κ' n ≤ k := Nat.sInf_le hkmem
    exact ⟨n, k, hndiv, hle, rfl⟩
  · intro hx
    have hxrep : ∃ n k : ℕ, ¬ ρ ∣ n ∧ κ' n ≤ k ∧ x = (n : ℝ) / (ρ : ℝ) ^ k := hx
    obtain ⟨n, k, hndiv, hκ'n, rfl⟩ := hxrep
    have hn0 : n ≠ 0 := by
      intro hzero
      subst hzero
      exact hndiv (dvd_zero ρ)
    have hneSet : {k : ℕ | κ n ≤ k ∧
        ∃ u, j ≤ u ∧ (n : ℝ) / (ρ : ℝ) ^ k ∈ selfSimilarLayer K u}.Nonempty := by
      have hmem0 : (n : ℝ) / (ρ : ℝ) ^ κ n ∈ K :=
        (mem_of_mem_diff hκ hndiv le_rfl).1
      have hne0 : (n : ℝ) / (ρ : ℝ) ^ κ n ≠ 0 := by
        apply div_ne_zero _ (pow_ne_zero _ (scalar_ne_zero hK))
        exact_mod_cast hn0
      obtain ⟨U₀, hU₀⟩ := exists_layer hK hmem0 hne0
      have hmem1 : (n : ℝ) / (ρ : ℝ) ^ (κ n + j) ∈ K :=
        (mem_of_mem_diff hκ hndiv (by omega : κ n ≤ κ n + j)).1
      have hne1 : (n : ℝ) / (ρ : ℝ) ^ (κ n + j) ≠ 0 := by
        apply div_ne_zero _ (pow_ne_zero _ (scalar_ne_zero hK))
        exact_mod_cast hn0
      obtain ⟨U, hU⟩ := exists_layer hK hmem1 hne1
      have hcore := layer_index_add hS hU₀ hU
      rw [add_mul] at hcore
      have hle : j ≤ j * μ := Nat.le_mul_of_pos_right _ (module_pos hK)
      have hum : j ≤ U := by omega
      exact ⟨κ n + j, by omega, U, hum, hU⟩
    have hSmem : κ' n ∈ {k : ℕ | κ n ≤ k ∧
        ∃ u, j ≤ u ∧ (n : ℝ) / (ρ : ℝ) ^ k ∈ selfSimilarLayer K u} :=
      Nat.sInf_mem hneSet
    obtain ⟨hκnS, uS, huSge, huSmem⟩ := hSmem
    have hmemKk : (n : ℝ) / (ρ : ℝ) ^ k ∈ K :=
      (mem_of_mem_diff hκ hndiv (by omega : κ n ≤ k)).1
    have hneKk : (n : ℝ) / (ρ : ℝ) ^ k ≠ 0 := by
      apply div_ne_zero _ (pow_ne_zero _ (scalar_ne_zero hK))
      exact_mod_cast hn0
    obtain ⟨U₁, hU₁⟩ := exists_layer hK hmemKk hneKk
    have hcore2 := layer_index_add hS huSmem hU₁
    have hle2 : κ' n * μ ≤ k * μ := by gcongr
    have hum2 : j ≤ U₁ := by omega
    refine ⟨?_, ?_⟩
    · exact (antitone_iterate hS hum2) hU₁.1
    · rw [Set.mem_singleton_iff]
      exact hneKk

private theorem layer_mem_smul_iff {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) (v : ℕ) (y : ℝ) :
    ρ * y ∈ selfSimilarLayer K v ↔ y ∈ selfSimilarLayer K (v + μ) := by
  have hρ : ρ ≠ 0 := (zero_lt_one.trans hK.1).ne'
  let e := Homeomorph.mulLeft₀ ρ hρ
  have comm : Function.Commute (Set.preimage e) derivedSet := by
    intro A
    ext z
    simp only [Set.mem_preimage, mem_derivedSet, ← Filter.comap_principal,
      e.isOpenEmbedding.accPt_comap_iff]
  have he : e '' derivedSet^[μ] K = K := hK.smul_derivedSet_iterate
  have pre : e ⁻¹' K = derivedSet^[μ] K := by
    conv_lhs => rw [← he, e.preimage_image]
  have shift (i : ℕ) : e ⁻¹' derivedSet^[i] K = derivedSet^[i + μ] K := by
    rw [Function.iterate_add_apply, ← pre]
    exact comm.iterate_right i K
  have hlayer : e ⁻¹' selfSimilarLayer K v = selfSimilarLayer K (v + μ) := by
    simp only [selfSimilarLayer, Set.preimage_sdiff, shift, Nat.add_right_comm v 1 μ]
  have hmem : y ∈ e ⁻¹' selfSimilarLayer K v ↔ y ∈ selfSimilarLayer K (v + μ) := by
    rw [hlayer]
  rw [Set.mem_preimage] at hmem
  exact hmem

private theorem mem_layer_mul_pow {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) {v j : ℕ} {y : ℝ}
    (hy : y ∈ selfSimilarLayer K (v + j * μ)) :
    ρ ^ j * y ∈ selfSimilarLayer K v := by
  induction j generalizing v y with
  | zero => simpa using hy
  | succ j ih =>
    have hidx : v + (j + 1) * μ = (v + μ) + j * μ := by rw [Nat.succ_mul]; omega
    rw [hidx] at hy
    have h1 := ih hy
    have hpow : ρ ^ (j + 1) * y = ρ * (ρ ^ j * y) := by rw [pow_succ', mul_assoc]
    rw [hpow]
    exact (layer_mem_smul_iff hK v _).mpr h1

private theorem layer_image_mul_pow {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) (v j : ℕ) :
    (fun y => ρ ^ j * y) '' selfSimilarLayer K (v + j * μ) = selfSimilarLayer K v := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_layer_mul_pow hK hy
  · intro hx
    have hρ : ρ ≠ 0 := (zero_lt_one.trans hK.1).ne'
    refine ⟨x / ρ ^ j, mem_layer_div_pow hK hx j, ?_⟩
    change ρ ^ j * (x / ρ ^ j) = x
    rw [mul_comm]
    exact div_mul_cancel₀ _ (pow_ne_zero j hρ)

private def shiftEnum (μ ρ n : ℕ) (t : ℕ → Ordinal.{0} → ℝ) : ℕ → Ordinal.{0} → ℝ :=
  fun v β => if n ≤ v then t (v - n) β else (ρ : ℝ) ^ n * t (v + n * μ - n) β

private theorem shiftEnum_eq_of_le (μ ρ n : ℕ) (t : ℕ → Ordinal.{0} → ℝ) {v : ℕ}
    (h : n ≤ v) (β : Ordinal.{0}) :
    shiftEnum μ ρ n t v β = t (v - n) β := by
  simp [shiftEnum, h]

private theorem shiftEnum_eq_of_not_le (μ ρ n : ℕ) (t : ℕ → Ordinal.{0} → ℝ) {v : ℕ}
    (h : ¬ n ≤ v) (β : Ordinal.{0}) :
    shiftEnum μ ρ n t v β = (ρ : ℝ) ^ n * t (v + n * μ - n) β := by
  simp [shiftEnum, h]

private theorem shiftEnum_anti {K : Set ℝ} {μ ρ : ℕ}
    (hKq : IsQuasiArithmeticalCompactSet K μ ρ) (n : ℕ)
    {t : ℕ → Ordinal.{0} → ℝ}
    (ht : ∀ u, StrictAntiOn (t u) (Set.Iio (ω ^ ω))) (v : ℕ) :
    StrictAntiOn (shiftEnum μ ρ n t v) (Set.Iio (ω ^ ω)) := by
  intro a ha b hb hab
  by_cases hvn : n ≤ v
  · rw [shiftEnum_eq_of_le μ ρ n t hvn b, shiftEnum_eq_of_le μ ρ n t hvn a]
    exact ht (v - n) ha hb hab
  · rw [shiftEnum_eq_of_not_le μ ρ n t hvn b, shiftEnum_eq_of_not_le μ ρ n t hvn a]
    have hρpos : (0 : ℝ) < ρ := zero_lt_one.trans (scalar_pos hKq)
    exact mul_lt_mul_of_pos_left (ht (v + n * μ - n) ha hb hab) (pow_pos hρpos n)

private theorem shiftEnum_onto {K : Set ℝ} {μ ρ : ℕ}
    (hKq : IsQuasiArithmeticalCompactSet K μ ρ) (n : ℕ)
    {t : ℕ → Ordinal.{0} → ℝ}
    (htK : ∀ u, t u '' Set.Iio (ω ^ ω) = selfSimilarLayer (derivedSet^[n] K) u)
    (v : ℕ) :
    shiftEnum μ ρ n t v '' Set.Iio (ω ^ ω) = selfSimilarLayer K v := by
  by_cases hvn : n ≤ v
  · have efun : shiftEnum μ ρ n t v = t (v - n) :=
      funext fun β => shiftEnum_eq_of_le μ ρ n t hvn β
    rw [efun, htK (v - n), layer_shift n (v - n)]
    congr 1
    omega
  · have efun : shiftEnum μ ρ n t v = fun β => (ρ : ℝ) ^ n * t (v + n * μ - n) β :=
      funext fun β => shiftEnum_eq_of_not_le μ ρ n t hvn β
    have himg : (fun β => (ρ : ℝ) ^ n * t (v + n * μ - n) β) '' Set.Iio (ω ^ ω)
        = (fun y => (ρ : ℝ) ^ n * y) '' (t (v + n * μ - n) '' Set.Iio (ω ^ ω)) := by
      ext x
      constructor
      · rintro ⟨β, hβ, rfl⟩
        exact ⟨t (v + n * μ - n) β, ⟨β, hβ, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨β, hβ, rfl⟩, rfl⟩
        exact ⟨β, hβ, rfl⟩
    have hle : n ≤ v + n * μ := by
      have hμ := Nat.le_mul_of_pos_right n (module_pos hKq)
      omega
    have hw : v + n * μ - n + n = v + n * μ := Nat.sub_add_cancel hle
    rw [efun, himg, htK (v + n * μ - n), layer_shift n (v + n * μ - n), hw]
    exact layer_image_mul_pow hKq.isSelfSimilarCompactSet v n

private theorem gaugeSet_eq {K : Set ℝ} {μ ρ : ℕ}
    (hKq : IsQuasiArithmeticalCompactSet K μ ρ) (n : ℕ) {m k : ℕ} (hm0 : m ≠ 0) :
    {x : ℝ | ∃ a b r : ℕ, m = a * b ∧
      stabilityGauge (derivedSet^[n] K) μ ρ m =
        stabilityGauge (derivedSet^[n] K) μ ρ a + stabilityGauge (derivedSet^[n] K) μ ρ b ∧
      x = b * (a * (ρ : ℝ) ^ r + 1) / (ρ : ℝ) ^ (r + k)}
    = {x : ℝ | ∃ a b r : ℕ, m = a * b ∧
      stabilityGauge K μ ρ m = stabilityGauge K μ ρ a + stabilityGauge K μ ρ b ∧
      x = b * (a * (ρ : ℝ) ^ r + 1) / (ρ : ℝ) ^ (r + k)} := by
  ext x
  constructor <;> rintro ⟨a, b, r, hm, hg, hx⟩
  · refine ⟨a, b, r, hm, ?_, hx⟩
    have ha0 : a ≠ 0 := fun hz => hm0 (by rw [hm, hz, zero_mul])
    have hb0 : b ≠ 0 := fun hz => hm0 (by rw [hm, hz, mul_zero])
    simpa only [gauge_eq hKq n (Nat.pos_of_ne_zero hm0),
      gauge_eq hKq n (Nat.pos_of_ne_zero ha0),
      gauge_eq hKq n (Nat.pos_of_ne_zero hb0)] using hg
  · refine ⟨a, b, r, hm, ?_, hx⟩
    have ha0 : a ≠ 0 := fun hz => hm0 (by rw [hm, hz, zero_mul])
    have hb0 : b ≠ 0 := fun hz => hm0 (by rw [hm, hz, mul_zero])
    simpa only [← gauge_eq hKq n (Nat.pos_of_ne_zero hm0),
      ← gauge_eq hKq n (Nat.pos_of_ne_zero ha0),
      ← gauge_eq hKq n (Nat.pos_of_ne_zero hb0)] using hg

end isArithmeticalCompactSet_derivedSet_iterate

open isArithmeticalCompactSet_derivedSet_iterate in
/-- **Derived sets of an arithmetical compact set are arithmetical (Proposition 7).** Let $K$ be
an arithmetical compact set of module $\mu$ and ratio $\rho$. For every natural number $n$, the
$n$-th derived set $K^{(n)}$ of $K$ (the set of accumulation points, iterated $n$ times, so that
$K^{(0)} = K$) is an arithmetical compact set of module $\mu$ and ratio $\rho$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 7. -/
public theorem isArithmeticalCompactSet_derivedSet_iterate {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsArithmeticalCompactSet K μ ρ) (n : ℕ) :
    IsArithmeticalCompactSet (derivedSet^[n] K) μ ρ := by
  refine ⟨quasi_transfer hK.1 n, ?_⟩
  intro t ht htK u α hα m k hmdiv heq
  have hm0 : m ≠ 0 := fun hz => hmdiv (by rw [hz]; exact dvd_zero ρ)
  have hs_eq : shiftEnum μ ρ n t (u + n + 1) α = (m : ℝ) / (ρ : ℝ) ^ k := by
    rw [shiftEnum_eq_of_le μ ρ n t (by omega) α]
    have hidx : u + n + 1 - n = u + 1 := by omega
    rw [hidx]
    exact heq
  have hfin := hK.2 (shiftEnum μ ρ n t) (shiftEnum_anti hK.1 n ht)
    (shiftEnum_onto hK.1 n htK) (u + n) α hα m k hmdiv hs_eq
  have hrange : (Set.range fun r : ℕ => t u (ω * α + r))
      = Set.range fun r : ℕ => shiftEnum μ ρ n t (u + n) (ω * α + r) := by
    congr 1
    funext r
    have hidx : u + n - n = u := Nat.add_sub_cancel u n
    rw [shiftEnum_eq_of_le μ ρ n t (by omega) _, hidx]
  rw [hrange, gaugeSet_eq hK.1 n hm0]
  exact hfin

end MetaMathlibExt
