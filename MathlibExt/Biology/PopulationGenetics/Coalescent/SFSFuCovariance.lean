/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFuDerivation
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Fu's branch-length covariances for every sample size

**Source.** Y.-X. Fu (1995), *Statistical properties of segregating sites*, Theor. Popul. Biol.
48, 172–197, Section 3: under Kingman's coalescent the total length `L_i` of the branches
subtending `i` of the `n` sample copies satisfies `Cov(L_i, L_j) = 4 σ_{ij}` with Fu's closed form
`σ_{ij}`. This file proves it for every sample size `n` and all `1 ≤ i, j ≤ n - 1`, discharging
the hypothesis `hσ` of `SFSFuClosedForm` (T114) from `randomJoining` and `KingmanTimes`.

**Source receipt (API-00).** Reused, not reproved:

* `SFSFuDerivation.covariance_sfsLength_eq_four_mul_fuSigma_of_fuTopologyCov` (T155, merged):
  `hσ` from the deterministic identity `fuTopologyCov n i j = 4 σ_{ij}`, where `fuTopologyCov`
  is built from the two-level moments `blockCountMoment` of random joining (`joinPair`) and the
  holding-time moments `kingmanTimeMoment` of `KingmanTimes`;
* `SiteFrequencySpectrum.joinStep_iterate_replicate` (merged): from `n` singletons, `n - k` steps
  of random joining give the uniform law on compositions of `n` into `k` parts (for order-free
  statistics); this change makes it and its composition helpers (`IsSymm`, `comps`,
  `sum_comps_succ`, `card_comps`, `sum_blockPairs_eq_powersetCard`, ...) public, without
  changing their statements;
* `SiteFrequencySpectrum.joinStep_iterate_count` and `sum_blockCount_mul_inv_choose_two`
  (merged): `E[c_{k,i}]` and `∑_k E[c_{k,i}] / C(k, 2) = 2 / i`;
* `SFSFuClosedForm.fuSigma`, `fuBeta` and the conditional theorems `*_of_fuSigma` (T114).

## Method

1. **Clade identity** (`sum_inv_choose_two_mul_joinStep_iterate`). For any list `b` of `k`
   block sizes, `∑_{l=2}^{k} C(l, 2)⁻¹ E_b[∑_{blocks at level l} φ(size)]` equals the sum over
   sub-multisets `s ⊆ b` of `2 / (|s| C(k, |s|)) · φ(Σ s)`: a set of `m` of `k` lineages forms one
   block for an expected time `2 / (m C(k, m))`. Proved by induction on `k` from one step of
   `joinStep`, with two double-counting identities over sub-multisets.
2. **Per-level moments** (`levelMoment_eq`, `sum_comps_count_mul_cladeStat`). Combining (1) at
   level `k` with the uniform-composition law turns `∑_{l ≤ k} C(l, 2)⁻¹ E[c_{k,i} c_{l,j}]` into
   an average over compositions, which `sum_comps_powersetCard` (splitting a composition along a
   sub-multiset of its parts) evaluates as a single sum over the subset size `m`; Vandermonde
   closes it (`sum_nested`, `sum_disjoint`, `levelMoment_closed`).
3. **Harmonic sums** (`sum_choose_sub_div`): `∑_{k=1}^{N} C(N-k, r) / k = C(N, r)(H_N - H_r)`,
   giving `∑_k C(n-i-1, k-2) / (C(n-1, k-1) C(k, 2)) = β_n(i)` and the `i + j = n` sum.
4. **Fu's six cases** (`fuHalfCov_add_fuHalfCov`), using `fuBeta_rec`:
   `(n - i + 1) β_n(i) - (n - i - 1) β_n(i + 1) = 2 / i`.

## Main results

* `fuTopologyCov_eq_four_mul_fuSigma`: `fuTopologyCov n i j = 4 σ_{ij}` for every `n` and
  `1 ≤ i, j ≤ n - 1` (T155 had it for `n ≤ 4`).
* `covariance_sfsLength_eq_four_mul_fuSigma`: **`hσ`**, `Cov(L_i, L_j) = 4 σ_{ij}`, from the
  random-joining law of the topology, the `KingmanTimes` holding times and their independence.
* `covariance_count_kingman_eq_fuSigma`: Fu's SFS covariance
  `Cov(ξ_i, ξ_j) = δ_{ij} θ / i + σ_{ij} θ²` for every sample size, and
  `variance_sum_kingman_eq_fuSigma`, `variance_sum_sfsLength_eq_fuSigma`: the variances of linear
  statistics, i.e. T114's conditional theorems with `hσ` discharged.

## References

* Y.-X. Fu, *Statistical properties of segregating sites*, Theor. Popul. Biol. 48 (1995),
  172–197.
* R. C. Griffiths, S. Tavaré, *The age of a mutation in a general coalescent tree*, Stoch. Models
  14 (1998), 273–295.
* J. F. C. Kingman, *The coalescent*, Stoch. Proc. Appl. 13 (1982), 235–248.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFuCovariance

open SiteFrequencySpectrum SFSCovariance SFSFuClosedForm SFSFuDerivation

/-! ### Double counting over sub-multisets -/

section DoubleCounting

variable {α : Type*} [DecidableEq α]

theorem sum_powersetCard_sum_powerset_add (a : ℕ) (B : Multiset α) (H : Multiset α → ℝ) :
    ((Multiset.powersetCard a B).map fun t => ((B - t).powerset.map fun s => H (t + s)).sum).sum =
      (B.powerset.map fun S => ((S.card.choose a : ℕ) : ℝ) * H S).sum := by
  induction B using Multiset.induction_on generalizing a H with
  | empty =>
    rcases a with _ | a
    · simp
    · rw [Multiset.powersetCard_eq_empty _ (by simp)]; simp
  | cons x B ih =>
    rcases a with _ | a
    · simp
    rw [Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map]
    have h1 : ∀ t ∈ Multiset.powersetCard (a + 1) B,
        (((x ::ₘ B) - t).powerset.map fun s => H (t + s)).sum =
          ((B - t).powerset.map fun s => H (t + s)).sum +
            ((B - t).powerset.map fun s => H (x ::ₘ (t + s))).sum := by
      intro t ht
      rw [Multiset.cons_sub_of_le x (Multiset.mem_powersetCard.1 ht).1, Multiset.powerset_cons,
        Multiset.map_add, Multiset.sum_add, Multiset.map_map]
      congr 2
      exact Multiset.map_congr rfl fun s _ => by simp [Multiset.add_cons]
    have h2 : ∀ t ∈ Multiset.powersetCard a B,
        (((x ::ₘ B) - x ::ₘ t).powerset.map fun s => H (x ::ₘ t + s)).sum =
          ((B - t).powerset.map fun s => H (x ::ₘ (t + s))).sum := by
      intro t _
      simp [Multiset.cons_add]
    have ih1 := ih (a + 1) (fun s => H (x ::ₘ s))
    have ih2 := ih a (fun s => H (x ::ₘ s))
    rw [Multiset.map_congr rfl h1, Function.comp_def, Multiset.map_congr rfl h2,
      Multiset.sum_map_add, ih, ih1, ih2, Multiset.powerset_cons, Multiset.map_add,
      Multiset.sum_add, Multiset.map_map, add_assoc, ← Multiset.sum_map_add]
    congr 2
    refine Multiset.map_congr rfl fun S _ => ?_
    simp only [Function.comp_apply, Multiset.card_cons, Nat.choose_succ_succ', Nat.cast_add]
    ring

theorem sum_powersetCard_sum_powerset_sub (a : ℕ) (B : Multiset α) (H : Multiset α → ℝ) :
    ((Multiset.powersetCard a B).map fun t => ((B - t).powerset.map H).sum).sum =
      (B.powerset.map fun S => (((B.card - S.card).choose a : ℕ) : ℝ) * H S).sum := by
  induction B using Multiset.induction_on generalizing a H with
  | empty =>
    rcases a with _ | a
    · simp
    · rw [Multiset.powersetCard_eq_empty _ (by simp)]; simp
  | cons x B ih =>
    rcases a with _ | a
    · simp
    rw [Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map]
    have h1 : ∀ t ∈ Multiset.powersetCard (a + 1) B,
        (((x ::ₘ B) - t).powerset.map H).sum =
          ((B - t).powerset.map H).sum + ((B - t).powerset.map fun s => H (x ::ₘ s)).sum := by
      intro t ht
      rw [Multiset.cons_sub_of_le x (Multiset.mem_powersetCard.1 ht).1, Multiset.powerset_cons,
        Multiset.map_add, Multiset.sum_add, Multiset.map_map]
      rfl
    have h2 : ∀ t ∈ Multiset.powersetCard a B,
        (((x ::ₘ B) - x ::ₘ t).powerset.map H).sum = ((B - t).powerset.map H).sum := by
      intro t _
      simp
    have ih1 := ih (a + 1) (fun s => H (x ::ₘ s))
    rw [Multiset.map_congr rfl h1, Function.comp_def, Multiset.map_congr rfl h2,
      Multiset.sum_map_add, ih, ih1, ih, Multiset.powerset_cons, Multiset.map_add,
      Multiset.sum_add, Multiset.map_map, add_comm (Multiset.sum _) (Multiset.sum _), add_assoc,
      ← Multiset.sum_map_add, add_comm]
    congr 1
    · refine congrArg Multiset.sum (Multiset.map_congr rfl fun S hS => ?_)
      have hle : S.card ≤ B.card := Multiset.card_le_card (Multiset.mem_powerset.1 hS)
      rw [Multiset.card_cons, show B.card + 1 - S.card = (B.card - S.card) + 1 by omega,
        Nat.choose_succ_succ', Nat.cast_add]
      ring
    · refine congrArg Multiset.sum (Multiset.map_congr rfl fun S _ => ?_)
      simp

omit [DecidableEq α] in
theorem sum_powerset_card_eq_zero (B : Multiset α) (g : Multiset α → ℝ) :
    (B.powerset.map fun s => if s.card = 0 then g s else 0).sum = g 0 := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons x B ih =>
    rw [Multiset.powerset_cons, Multiset.map_add, Multiset.sum_add, ih, Multiset.map_map]
    simp

theorem sum_powerset_card_eq_one (B : Multiset ℕ) (φ : ℕ → ℝ) :
    (B.powerset.map fun s => if s.card = 1 then φ s.sum else 0).sum = (B.map φ).sum := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons x B ih =>
    rw [Multiset.powerset_cons, Multiset.map_add, Multiset.sum_add, ih, Multiset.map_map]
    have h2 : (B.powerset.map ((fun s => if s.card = 1 then φ s.sum else 0) ∘ Multiset.cons x)) =
        B.powerset.map fun s => if s.card = 0 then φ (x + s.sum) else 0 :=
      Multiset.map_congr rfl fun s _ => by simp
    rw [h2, sum_powerset_card_eq_zero B (fun s => φ (x + s.sum)), Multiset.map_cons,
      Multiset.sum_cons]
    simp [add_comm]


end DoubleCounting

/-! ### Clade weights and the time-weighted block counts of random joining -/

/-- The weight `2 / (m · C(k, m))` of a set of `m` of `k` blocks (`0` unless `1 ≤ m < k`): the
expected total time, in units of `E T`, during which a given set of `m` of `k` lineages forms
exactly one block of Kingman's coalescent (from level `k` down, level `k` included). -/
noncomputable def cladeWeight (k m : ℕ) : ℝ :=
  if 1 ≤ m ∧ m < k then 2 / ((m : ℝ) * (k.choose m : ℝ)) else 0

theorem cladeWeight_of {k m : ℕ} (h1 : 1 ≤ m) (h2 : m < k) :
    cladeWeight k m = 2 / ((m : ℝ) * (k.choose m : ℝ)) := by
  unfold cladeWeight
  split_ifs with h
  · rfl
  · exact absurd ⟨h1, h2⟩ h

theorem cladeWeight_of_not {k m : ℕ} (h : ¬ (1 ≤ m ∧ m < k)) : cladeWeight k m = 0 := by
  unfold cladeWeight
  split_ifs
  rfl

theorem cladeWeight_succ (k m : ℕ) (hm : m ≤ k + 2) :
    ((k + 2).choose 2 : ℝ)⁻¹ * (if m = 1 then 1 else 0) +
      ((((k + 2 - m).choose 2 : ℕ) : ℝ) * cladeWeight (k + 1) m +
        ((m.choose 2 : ℕ) : ℝ) * cladeWeight (k + 1) (m - 1)) / ((k + 2).choose 2 : ℝ) =
      cladeWeight (k + 2) m := by
  have hC2 : ((k + 2).choose 2 : ℝ) = (k + 2) * (k + 1) / 2 := by
    rw [Nat.cast_choose_two]; push_cast; ring
  rcases Nat.lt_or_ge m 2 with h | h
  · interval_cases m
    · simp [cladeWeight]
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · norm_num [cladeWeight]
      · rw [cladeWeight_of le_rfl (by omega : 1 < k + 1), 
          cladeWeight_of le_rfl (by omega : 1 < k + 2),
          cladeWeight_of_not (by omega : ¬ (1 ≤ 1 - 1 ∧ 1 - 1 < k + 1)), hC2,
          show k + 2 - 1 = k + 1 by omega, Nat.cast_choose_two]
        simp only [Nat.choose_one_right, ↓reduceIte]
        push_cast
        field_simp
        ring
  · rcases Nat.eq_or_lt_of_le hm with rfl | hm'
    · rw [cladeWeight_of_not (by omega), cladeWeight_of_not (by omega),
        cladeWeight_of_not (by omega)]
      simp
    obtain ⟨p, rfl⟩ : ∃ p, m = p + 2 := ⟨m - 2, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, k = p + q + 1 := ⟨k - p - 1, by omega⟩
    rw [show p + q + 1 + 2 - (p + 2) = q + 1 by omega, show p + 2 - 1 = p + 1 by omega,
      show p + q + 1 + 1 = p + q + 2 by ring] at *
    set x : ℝ := ((p + q + 2).choose (p + 1) : ℝ) with hxdef
    set y : ℝ := ((p + q + 2).choose (p + 2) : ℝ) with hydef
    have hx : (0 : ℝ) < x := by rw [hxdef]; exact_mod_cast Nat.choose_pos (by omega)
    have hpas : ((p + q + 1 + 2).choose (p + 2) : ℝ) = y + x := by
      have := Nat.choose_succ_succ' (p + q + 2) (p + 1)
      rw [show p + q + 2 + 1 = p + q + 1 + 2 by ring, show p + 1 + 1 = p + 2 by ring] at this
      rw [hxdef, hydef]; exact_mod_cast (this.trans (add_comm _ _))
    have hrat : y = x * (q + 1) / (p + 2) := by
      have := Nat.choose_succ_right_eq (p + q + 2) (p + 1)
      rw [show p + q + 2 - (p + 1) = q + 1 by omega] at this
      rw [eq_div_iff (by positivity), hxdef, hydef]
      exact_mod_cast this
    have hW1 : (((q + 1).choose 2 : ℕ) : ℝ) * cladeWeight (p + q + 2) (p + 2) =
        (((q + 1).choose 2 : ℕ) : ℝ) * (2 / (((p + 2 : ℕ) : ℝ) * y)) := by
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · simp
      · rw [cladeWeight_of (by omega) (by omega), hydef]
    simp only [show p + 2 ≠ 1 by omega, ↓reduceIte, mul_zero, zero_add]
    rw [hW1, cladeWeight_of (by omega) (by omega), cladeWeight_of (by omega) (by omega),
      hC2, hpas, ← hxdef, hrat, Nat.cast_choose_two, Nat.cast_choose_two]
    push_cast
    field_simp
    ring


/-- The clade statistic of a multiset `B` of `k` block sizes: the sum over all sub-multisets `s`
(with multiplicity) of `cladeWeight k |s| · φ(Σ s)`. -/
noncomputable def cladeStat (k : ℕ) (φ : ℕ → ℝ) (B : Multiset ℕ) : ℝ :=
  (B.powerset.map fun s => cladeWeight k s.card * φ s.sum).sum

theorem joinStep_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (f : ι → List ℕ → ℝ)
    (b : List ℕ) :
    joinStep (fun y => ∑ l ∈ s, a l * f l y) b = ∑ l ∈ s, a l * joinStep (f l) b := by
  unfold joinStep
  split_ifs
  · rfl
  · rw [sum_comm, sum_div]
    refine sum_congr rfl fun l _ => ?_
    rw [← mul_sum, mul_div_assoc]

theorem card_blockPairs_length (b : List ℕ) :
    ((blockPairs b.length).card : ℝ) = ((b.length.choose 2 : ℕ) : ℝ) := by
  have := sum_blockPairs_eq_powersetCard b (fun _ => 1)
  simp only [sum_const, nsmul_eq_mul, mul_one, Multiset.map_const', Multiset.sum_replicate,
    Multiset.card_powersetCard, Multiset.coe_card] at this
  exact this

theorem length_mergeBlocks {b : List ℕ} {p : ℕ × ℕ} (hp : p ∈ blockPairs b.length) :
    (mergeBlocks b p.1 p.2).length = b.length - 1 := by
  simp only [blockPairs, mem_filter, mem_product, mem_range] at hp
  rw [mergeBlocks, List.length_append, List.length_eraseIdx_of_lt (by
    rw [List.length_eraseIdx_of_lt hp.1.2]; omega), List.length_eraseIdx_of_lt hp.1.2]
  simp only [List.length_singleton]
  omega

/-- **Time-weighted future block counts of random joining.** For a list `b` of `k` block sizes
and a statistic `φ` of a block size, the expected value of `∑_{l=2}^{k} T̄_l ∑_{blocks B at level
l} φ(|B|)` under random joining from `b`, with `T̄_l = 1 / C(l, 2)`, is the clade statistic
`∑_{s ⊆ b} 2 / (|s| C(k, |s|)) · φ(Σ s)` (over sub-multisets `s` with `1 ≤ |s| < k`). -/
theorem sum_inv_choose_two_mul_joinStep_iterate (φ : ℕ → ℝ) :
    ∀ (k : ℕ) (b : List ℕ), b.length = k →
      ∑ l ∈ Icc 2 k, ((l.choose 2 : ℕ) : ℝ)⁻¹ * (joinStep^[k - l] fun y => (y.map φ).sum) b =
        cladeStat k φ b
  | 0, b, _ => by
    have h0 : ∀ m, cladeWeight 0 m = 0 := fun m => cladeWeight_of_not (by omega)
    rw [cladeStat]
    simp only [h0, zero_mul, Multiset.map_const', Multiset.sum_replicate, smul_zero]
    simp
  | 1, b, _ => by
    have h0 : ∀ m, cladeWeight 1 m = 0 := fun m => cladeWeight_of_not (by omega)
    rw [cladeStat]
    simp only [h0, zero_mul, Multiset.map_const', Multiset.sum_replicate, smul_zero]
    simp
  | k + 2, b, hb => by
    have ih := sum_inv_choose_two_mul_joinStep_iterate φ (k + 1)
    set G : List ℕ → ℝ := fun y => (y.map φ).sum with hG
    rw [show k + 2 = k + 1 + 1 by ring, sum_Icc_succ_top (by omega), Nat.sub_self,
      Function.iterate_zero, id]
    have hsucc : ∀ l ∈ Icc 2 (k + 1), ((l.choose 2 : ℕ) : ℝ)⁻¹ * (joinStep^[k + 1 + 1 - l] G) b =
        ((l.choose 2 : ℕ) : ℝ)⁻¹ * joinStep (joinStep^[k + 1 - l] G) b := by
      intro l hl
      rw [show k + 1 + 1 - l = (k + 1 - l) + 1 by have := (mem_Icc.1 hl).2; omega,
        Function.iterate_succ_apply']
    rw [sum_congr rfl hsucc, ← joinStep_sum]
    have hcard : (blockPairs b.length).card ≠ 0 := by
      intro h
      have := card_blockPairs_length b
      rw [h, hb] at this
      simp only [Nat.cast_zero] at this
      have h2 : 0 < (k + 1 + 1).choose 2 := Nat.choose_pos (by omega)
      exact absurd this.symm (by exact_mod_cast h2.ne')
    have hmerge : ∀ p ∈ blockPairs b.length,
        (∑ l ∈ Icc 2 (k + 1), ((l.choose 2 : ℕ) : ℝ)⁻¹ * (joinStep^[k + 1 - l] G)
          (mergeBlocks b p.1 p.2)) = cladeStat (k + 1) φ (mergeBlocks b p.1 p.2) := by
      intro p hp
      exact ih _ (by rw [length_mergeBlocks hp, hb]; omega)
    simp only [joinStep, hcard, ↓reduceIte]
    rw [sum_congr rfl hmerge,
      sum_blockPairs_eq_powersetCard b (cladeStat (k + 1) φ), card_blockPairs_length, hb]
    set B : Multiset ℕ := (b : Multiset ℕ) with hB
    have hBcard : B.card = k + 1 + 1 := by rw [hB, Multiset.coe_card, hb]
    -- expand the clade statistic of a merged multiset
    have hexp : ∀ t ∈ Multiset.powersetCard 2 B, cladeStat (k + 1) φ (t.sum ::ₘ (B - t)) =
        ((B - t).powerset.map fun s => cladeWeight (k + 1) s.card * φ s.sum).sum +
          ((B - t).powerset.map fun s =>
            cladeWeight (k + 1) ((t + s).card - 1) * φ (t + s).sum).sum := by
      intro t ht
      have htc : t.card = 2 := (Multiset.mem_powersetCard.1 ht).2
      rw [cladeStat, Multiset.powerset_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map]
      congr 2
      refine Multiset.map_congr rfl fun s _ => ?_
      simp only [Function.comp_apply, Multiset.card_cons, Multiset.sum_cons, Multiset.card_add,
        Multiset.sum_add, htc]
      congr 2
      omega
    have hGb : G b = (B.map φ).sum := by rw [hG, hB, Multiset.map_coe, Multiset.sum_coe]
    rw [Multiset.map_congr rfl hexp, Multiset.sum_map_add, sum_powersetCard_sum_powerset_sub,
      sum_powersetCard_sum_powerset_add 2 B
        (fun S => cladeWeight (k + 1) (S.card - 1) * φ S.sum), hBcard, hGb,
      ← sum_powerset_card_eq_one B φ, cladeStat, show k + 1 + 1 = k + 2 by ring,
      div_eq_mul_inv, ← Multiset.sum_map_add, ← Multiset.sum_map_mul_right,
      ← Multiset.sum_map_mul_left, ← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun S hS => ?_)
    have hle : S.card ≤ k + 2 := by
      have := Multiset.card_le_card (Multiset.mem_powerset.1 hS)
      omega
    rw [← cladeWeight_succ k S.card hle]
    split_ifs <;> ring

/-! ### Sums over uniform compositions -/

theorem sum_comps_zero {M : Type*} [AddCommMonoid M] (N : ℕ) (F : (Fin 0 → ℕ) → M) :
    ∑ c ∈ comps N 0, F c = if N = 0 then F Fin.elim0 else 0 := by
  have hc : comps N 0 = if N = 0 then {Fin.elim0} else ∅ := by
    ext c
    rw [mem_comps]
    simp only [Finset.univ_eq_empty, sum_empty, IsEmpty.forall_iff, true_and]
    split_ifs with h
    · simp only [mem_singleton, h, true_iff]
      exact Subsingleton.elim _ _
    · simp only [Finset.notMem_empty, iff_false]
      omega
  rw [hc]
  split_ifs <;> simp

theorem card_comps_eq (y r : ℕ) : ((comps y r).card : ℝ) =
    if r = 0 then (if y = 0 then 1 else 0)
    else if y = 0 then 0 else ((y - 1).choose (r - 1) : ℝ) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have := sum_comps_zero y (fun _ => (1 : ℝ))
    simp only [sum_const, nsmul_eq_mul, mul_one] at this
    rw [this]
    simp
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · have : comps 0 r = ∅ := by
      refine eq_empty_of_forall_notMem fun c hc => ?_
      rw [mem_comps] at hc
      have : ∑ t : Fin r, 1 ≤ ∑ t, c t := sum_le_sum fun t _ => hc.1 t
      simp [hc.2] at this
      omega
    simp [this, hr.ne']
  · rw [card_comps hr hy]
    simp [hr.ne', hy.ne']

theorem sum_comps_succ_ofFn (y m : ℕ) (H : Multiset ℕ → ℝ) :
    ∑ u ∈ comps y (m + 1), H (List.ofFn u) =
      ∑ a ∈ Icc 1 y, ∑ u ∈ comps (y - a) m, H (a ::ₘ (List.ofFn u : Multiset ℕ)) := by
  rw [← sum_comps_succ y m (fun a u => H (a ::ₘ (List.ofFn u : Multiset ℕ)))]
  refine sum_congr rfl fun c _ => ?_
  rw [List.ofFn_succ, ← Multiset.cons_coe]

private theorem sum_Icc_range_comm (N : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ a ∈ Icc 1 N, ∑ x ∈ range (N - a + 1), f a x =
      ∑ x ∈ range (N + 1), ∑ a ∈ Icc 1 (N - x), f a x :=
  sum_comm' fun a x => by simp only [mem_Icc, mem_range]; omega

private theorem sum_Icc_range_add (N : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ a ∈ Icc 1 N, ∑ x ∈ range (N - a + 1), g a (a + x) =
      ∑ y ∈ range (N + 1), ∑ a ∈ Icc 1 y, g a y := by
  have h : ∀ a ∈ Icc 1 N, ∑ x ∈ range (N - a + 1), g a (a + x) = ∑ y ∈ Icc a N, g a y := by
    intro a ha
    have ha' := (mem_Icc.1 ha)
    refine sum_nbij' (a + ·) (· - a) ?_ ?_ ?_ ?_ ?_ <;> intro x hx <;>
      simp only [mem_Icc, mem_range] at hx ⊢ <;> omega
  rw [sum_congr rfl h]
  exact sum_comm' fun a y => by simp only [mem_Icc, mem_range]; omega

theorem sum_comps_powersetCard_zero (H K : Multiset ℕ → ℝ) (k N : ℕ) :
    ∑ c ∈ comps N k, ((Multiset.powersetCard 0 (List.ofFn c : Multiset ℕ)).map
        fun s => H s * K ((List.ofFn c : Multiset ℕ) - s)).sum =
      (k.choose 0 : ℝ) * ∑ x ∈ range (N + 1),
        (∑ u ∈ comps x 0, H (List.ofFn u)) * ∑ v ∈ comps (N - x) (k - 0), K (List.ofFn v) := by
  simp only [Multiset.powersetCard_zero_left, Multiset.map_singleton, Multiset.sum_singleton,
    tsub_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, sum_comps_zero, ite_mul, zero_mul]
  rw [sum_ite_eq' (range (N + 1)) 0]
  simp only [mem_range, show 0 < N + 1 by omega, ↓reduceIte]
  rw [← mul_sum]
  simp

/-- **Splitting a uniform composition along a sub-multiset of its parts.** Summing a product
statistic `H(s) K(B \ s)` over the `m`-element sub-multisets `s` of the parts `B` of every
composition of `N` into `k` parts gives `C(k, m)` times the convolution of the sums of `H` over
compositions into `m` parts and of `K` over compositions into `k - m` parts. -/
theorem sum_comps_powersetCard (H K : Multiset ℕ → ℝ) (k N m : ℕ) :
    ∑ c ∈ comps N k, ((Multiset.powersetCard m (List.ofFn c : Multiset ℕ)).map
        fun s => H s * K ((List.ofFn c : Multiset ℕ) - s)).sum =
      (k.choose m : ℝ) * ∑ x ∈ range (N + 1),
        (∑ u ∈ comps x m, H (List.ofFn u)) * ∑ v ∈ comps (N - x) (k - m), K (List.ofFn v) := by
  induction k generalizing N m H K with
  | zero =>
    rcases m with _ | m
    · exact sum_comps_powersetCard_zero H K 0 N
    · rw [sum_comps_zero]
      simp only [List.ofFn_zero, Multiset.coe_nil,
        Multiset.powersetCard_eq_empty _ (show (0 : Multiset ℕ).card < m + 1 by simp)]
      simp
  | succ k ih =>
    rcases m with _ | m
    · exact sum_comps_powersetCard_zero H K (k + 1) N
    have hL : ∑ c ∈ comps N (k + 1), ((Multiset.powersetCard (m + 1) (List.ofFn c : Multiset ℕ)).map
        fun s => H s * K ((List.ofFn c : Multiset ℕ) - s)).sum =
        ∑ a ∈ Icc 1 N, ∑ r ∈ comps (N - a) k,
          (((Multiset.powersetCard (m + 1) (List.ofFn r : Multiset ℕ)).map
            fun s => H s * K (a ::ₘ ((List.ofFn r : Multiset ℕ) - s))).sum +
          ((Multiset.powersetCard m (List.ofFn r : Multiset ℕ)).map
            fun s => H (a ::ₘ s) * K ((List.ofFn r : Multiset ℕ) - s)).sum) := by
      rw [← sum_comps_succ N k (fun a r =>
        (((Multiset.powersetCard (m + 1) (List.ofFn r : Multiset ℕ)).map
            fun s => H s * K (a ::ₘ ((List.ofFn r : Multiset ℕ) - s))).sum +
          ((Multiset.powersetCard m (List.ofFn r : Multiset ℕ)).map
            fun s => H (a ::ₘ s) * K ((List.ofFn r : Multiset ℕ) - s)).sum))]
      refine sum_congr rfl fun c _ => ?_
      rw [List.ofFn_succ, ← Multiset.cons_coe, Multiset.powersetCard_cons, Multiset.map_add,
        Multiset.sum_add, Multiset.map_map]
      congr 1
      · refine congrArg Multiset.sum (Multiset.map_congr rfl fun s hs => ?_)
        rw [Multiset.cons_sub_of_le _ (Multiset.mem_powersetCard.1 hs).1]
      · refine congrArg Multiset.sum (Multiset.map_congr rfl fun s _ => ?_)
        simp
    rw [hL]
    simp only [sum_add_distrib]
    have e1 : ∀ a, ∑ r ∈ comps (N - a) k,
        ((Multiset.powersetCard (m + 1) (List.ofFn r : Multiset ℕ)).map
            fun s => H s * K (a ::ₘ ((List.ofFn r : Multiset ℕ) - s))).sum =
        (k.choose (m + 1) : ℝ) * ∑ x ∈ range (N - a + 1),
          (∑ u ∈ comps x (m + 1), H (List.ofFn u)) *
            ∑ v ∈ comps (N - a - x) (k - (m + 1)), K (a ::ₘ (List.ofFn v : Multiset ℕ)) :=
      fun a => ih H (fun s => K (a ::ₘ s)) (N - a) (m + 1)
    have e2 : ∀ a, ∑ r ∈ comps (N - a) k,
        ((Multiset.powersetCard m (List.ofFn r : Multiset ℕ)).map
            fun s => H (a ::ₘ s) * K ((List.ofFn r : Multiset ℕ) - s)).sum =
        (k.choose m : ℝ) * ∑ x ∈ range (N - a + 1),
          (∑ u ∈ comps x m, H (a ::ₘ (List.ofFn u : Multiset ℕ))) *
            ∑ v ∈ comps (N - a - x) (k - m), K (List.ofFn v) :=
      fun a => ih (fun s => H (a ::ₘ s)) K (N - a) m
    simp only [e1, e2, ← mul_sum]
    rw [Nat.add_sub_add_right, Nat.choose_succ_succ', Nat.cast_add, add_mul,
      add_comm ((k.choose (m + 1) : ℝ) * _)]
    congr 1
    · congr 1
      have h := sum_Icc_range_add N (fun a y =>
        (∑ u ∈ comps (y - a) m, H (a ::ₘ (List.ofFn u : Multiset ℕ))) *
          ∑ v ∈ comps (N - y) (k - m), K (List.ofFn v))
      simp only [Nat.add_sub_cancel_left, show ∀ a x, N - (a + x) = N - a - x from
        fun a x => by omega] at h
      rw [h]
      refine sum_congr rfl fun y _ => ?_
      rw [sum_comps_succ_ofFn, sum_mul]
    · rcases Nat.lt_or_ge k (m + 1) with hkm | hkm
      · simp [Nat.choose_eq_zero_of_lt hkm]
      congr 1
      rw [sum_Icc_range_comm]
      refine sum_congr rfl fun x hx => ?_
      rw [← mul_sum]
      congr 1
      rw [show k - m = (k - (m + 1)) + 1 by omega, sum_comps_succ_ofFn]
      refine sum_congr rfl fun a ha => ?_
      rw [show N - a - x = N - x - a by omega]

theorem sum_comps_count_ofFn (x m i : ℕ) (hi : 1 ≤ i) :
    ∑ u ∈ comps x m, ((List.ofFn u).count i : ℝ) =
      m * (if i ≤ x then ((comps (x - i) (m - 1)).card : ℝ) else 0) := by
  rcases m with _ | m
  · simp
  rw [Nat.add_sub_cancel]
  simp only [count_ofFn]
  rw [sum_comm]
  have ht : ∀ t : Fin (m + 1), ∑ c ∈ comps x (m + 1), (if c t = i then (1 : ℝ) else 0) =
      ∑ c ∈ comps x (m + 1), (if c 0 = i then (1 : ℝ) else 0) := by
    intro t
    rw [← sum_comps_comp_perm (Equiv.swap 0 t) (fun c => if c t = i then (1 : ℝ) else 0)]
    simp only [Function.comp_apply, Equiv.swap_apply_right]
  rw [sum_congr rfl fun t _ => ht t, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  congr 1
  rw [sum_comps_succ x m (fun a _ => if a = i then (1 : ℝ) else 0)]
  simp only [sum_const, nsmul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq' (Icc 1 x) i]
  simp only [mem_Icc, hi, true_and]

theorem sum_ofFn_of_mem_comps {x m : ℕ} {u : Fin m → ℕ} (hu : u ∈ comps x m) :
    (List.ofFn u : Multiset ℕ).sum = x := by
  rw [Multiset.sum_coe, List.sum_ofFn]
  exact (mem_comps.1 hu).2

theorem count_coe_ofFn {k : ℕ} (c : Fin k → ℕ) (i : ℕ) :
    ((List.ofFn c : Multiset ℕ).count i : ℝ) = ((List.ofFn c).count i : ℝ) := by
  rw [Multiset.coe_count]

/-- The indicator statistic of block size `j`. -/
noncomputable def sizeInd (j : ℕ) (x : ℕ) : ℝ := if x = j then 1 else 0

/-- **The per-level moment of the clade statistic over uniform compositions**, as a sum over the
size `m` of the sub-multiset. -/
theorem sum_comps_count_mul_cladeStat (n k i j : ℕ) (hi : 1 ≤ i) (hjn : j ≤ n) :
    ∑ c ∈ comps n k, ((List.ofFn c).count i : ℝ) * cladeStat k (sizeInd j) (List.ofFn c) =
      ∑ m ∈ range (k + 1), cladeWeight k m * (k.choose m : ℝ) *
        (m * (if i ≤ j then ((comps (j - i) (m - 1)).card : ℝ) else 0) *
            ((comps (n - j) (k - m)).card : ℝ) +
          ((comps j m).card : ℝ) * ((k - m : ℕ) *
            (if i ≤ n - j then ((comps (n - j - i) (k - m - 1)).card : ℝ) else 0))) := by
  have hB : ∀ c ∈ comps n k, ((List.ofFn c).count i : ℝ) *
      cladeStat k (sizeInd j) (List.ofFn c) =
      ∑ m ∈ range (k + 1), cladeWeight k m *
        (((Multiset.powersetCard m (List.ofFn c : Multiset ℕ)).map fun s =>
            sizeInd j s.sum * (s.count i : ℝ) * 1).sum +
          ((Multiset.powersetCard m (List.ofFn c : Multiset ℕ)).map fun s =>
            sizeInd j s.sum * ((((List.ofFn c : Multiset ℕ) - s).count i : ℕ) : ℝ)).sum) := by
    intro c _
    have hcard : (List.ofFn c : Multiset ℕ).card = k := by simp
    rw [cladeStat, ← Multiset.bind_powerset_len, Multiset.map_bind, Multiset.sum_bind, hcard]
    change _ * (Multiset.map _ (Finset.range (k + 1)).val).sum = _
    rw [← Finset.sum_eq_multiset_sum, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [← Multiset.sum_map_add, ← Multiset.sum_map_mul_left, ← Multiset.sum_map_mul_left]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun s hs => ?_)
    have hle : s ≤ (List.ofFn c : Multiset ℕ) := (Multiset.mem_powersetCard.1 hs).1
    have hcount : ((List.ofFn c).count i : ℝ) =
        (s.count i : ℝ) + ((((List.ofFn c : Multiset ℕ) - s).count i : ℕ) : ℝ) := by
      rw [← count_coe_ofFn, ← Nat.cast_add, ← Multiset.count_add, add_tsub_cancel_of_le hle]
    rw [hcount, (Multiset.mem_powersetCard.1 hs).2]
    ring
  rw [sum_congr rfl hB, sum_comm]
  refine sum_congr rfl fun m _ => ?_
  rw [← mul_sum, sum_add_distrib,
    sum_comps_powersetCard (fun s => sizeInd j s.sum * (s.count i : ℝ)) (fun _ => 1) k n m,
    mul_assoc, mul_assoc]
  have h2 := sum_comps_powersetCard (fun s => sizeInd j s.sum)
    (fun s => ((s.count i : ℕ) : ℝ)) k n m
  rw [h2]
  congr 1
  rw [← mul_add]
  congr 1
  have hcol : ∀ (F : ℕ → ℝ) (G : (Fin m → ℕ) → ℝ),
      ∑ x ∈ range (n + 1), (∑ u ∈ comps x m, sizeInd j (List.ofFn u : Multiset ℕ).sum * G u) *
        F x = (∑ u ∈ comps j m, G u) * F j := by
    intro F G
    have : ∀ x ∈ range (n + 1), (∑ u ∈ comps x m, sizeInd j (List.ofFn u : Multiset ℕ).sum * G u) *
        F x = if x = j then (∑ u ∈ comps j m, G u) * F j else 0 := by
      intro x _
      rw [sum_congr rfl fun u hu => by rw [sum_ofFn_of_mem_comps hu]]
      unfold sizeInd
      split_ifs with h
      · subst h; simp
      · simp
    rw [sum_congr rfl this, sum_ite_eq' (range (n + 1)) j]
    simp [hjn]
  have e1 := hcol (fun x => ∑ v ∈ comps (n - x) (k - m), (1 : ℝ))
    (fun u => ((List.ofFn u : Multiset ℕ).count i : ℝ))
  have e2 := hcol (fun x => ∑ v ∈ comps (n - x) (k - m),
      (((List.ofFn v : Multiset ℕ).count i : ℕ) : ℝ)) (fun _ => 1)
  simp only [mul_one] at e2
  rw [e1, e2]
  simp only [count_coe_ofFn, sum_comps_count_ofFn _ _ _ hi, sum_const, nsmul_eq_mul, mul_one]
  ring

/-! ### From `fuTopologyCov` to per-level moments -/

theorem joinStep_iterate_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (f : ι → List ℕ → ℝ)
    (r : ℕ) (b : List ℕ) :
    (joinStep^[r] fun y => ∑ l ∈ s, a l * f l y) b = ∑ l ∈ s, a l * (joinStep^[r] (f l)) b := by
  induction r generalizing b with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', show (joinStep^[r] fun y => ∑ l ∈ s, a l * f l y) =
      fun y => ∑ l ∈ s, a l * (joinStep^[r] (f l)) y from funext ih, joinStep_sum]
    simp only [Function.iterate_succ_apply']

theorem isSymm_joinStep_iterate {g : List ℕ → ℝ} (hg : IsSymm g) (r : ℕ) :
    IsSymm (joinStep^[r] g) := by
  induction r generalizing g with
  | zero => exact hg
  | succ r ih =>
    rw [Function.iterate_succ]
    exact ih (isSymm_joinStep hg)

theorem count_eq_sum_sizeInd (j : ℕ) (y : List ℕ) :
    ((y.count j : ℕ) : ℝ) = (y.map (sizeInd j)).sum := by
  induction y with
  | nil => simp
  | cons a y ih =>
    rw [List.count_cons, List.map_cons, List.sum_cons, ← ih, sizeInd]
    by_cases h : a = j
    · subst h; simp; ring
    · simp [h]

/-- The `T̄`-weighted moment at level `k`: `∑_{l=2}^{k} T̄_l E[c_{k,i} c_{l,j}]`. -/
noncomputable def levelMoment (n k i j : ℕ) : ℝ :=
  ∑ l ∈ Icc 2 k, ((l.choose 2 : ℕ) : ℝ)⁻¹ *
    joinPair (n - k) (n - l) (fun b => (b.count i : ℝ)) (fun b => (b.count j : ℝ))
      (List.replicate n 1)

/-- The level moment as an average over uniform compositions of the clade statistic. -/
theorem levelMoment_eq (n k i j : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    levelMoment n k i j * ((n - 1).choose (k - 1) : ℝ) =
      ∑ c ∈ comps n k, ((List.ofFn c).count i : ℝ) * cladeStat k (sizeInd j) (List.ofFn c) := by
  set Ψ : List ℕ → ℝ := fun y => ∑ l ∈ Icc 2 k, ((l.choose 2 : ℕ) : ℝ)⁻¹ *
    (joinStep^[k - l] fun b => (b.count j : ℝ)) y with hΨ
  have hlm : levelMoment n k i j =
      (joinStep^[n - k] fun y => (y.count i : ℝ) * Ψ y) (List.replicate n 1) := by
    rw [levelMoment]
    have : ∀ l ∈ Icc 2 k, ((l.choose 2 : ℕ) : ℝ)⁻¹ *
        joinPair (n - k) (n - l) (fun b => (b.count i : ℝ)) (fun b => (b.count j : ℝ))
          (List.replicate n 1) =
        ((l.choose 2 : ℕ) : ℝ)⁻¹ * (joinStep^[n - k] fun y => (y.count i : ℝ) *
          (joinStep^[k - l] fun b => (b.count j : ℝ)) y) (List.replicate n 1) := by
      intro l hl
      rw [joinPair, show n - l - (n - k) = k - l by have := (mem_Icc.1 hl); omega]
    rw [sum_congr rfl this, ← joinStep_iterate_sum]
    refine congrFun (congrArg (fun F => joinStep^[n - k] F) (funext fun y => ?_)) _
    rw [hΨ, mul_sum]
    exact sum_congr rfl fun l _ => by ring
  have hsymm : IsSymm fun y => (y.count i : ℝ) * Ψ y := by
    intro l l' h
    simp only [hΨ, h.count_eq]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    rw [isSymm_joinStep_iterate (fun a b h => by simp only [h.count_eq]) _ l l' h]
  have hrep := joinStep_iterate_replicate (N := n) (n - k) (by omega) _ hsymm
  rw [show n - (n - k) = k by omega,
    Nat.choose_symm_of_eq_add (show n - 1 = (n - k) + (k - 1) by omega)] at hrep
  rw [hlm, hrep]
  refine sum_congr rfl fun c _ => ?_
  congr 1
  have hcount : (fun b : List ℕ => ((b.count j : ℕ) : ℝ)) = fun y => (y.map (sizeInd j)).sum :=
    funext (count_eq_sum_sizeInd j)
  rw [hΨ, hcount]
  exact sum_inv_choose_two_mul_joinStep_iterate (sizeInd j) k _ (by simp)

private theorem kingmanTimeMoment_eq (k l : ℕ) :
    kingmanTimeMoment k l = ((k.choose 2 : ℕ) : ℝ)⁻¹ * ((l.choose 2 : ℕ) : ℝ)⁻¹ *
      ((if l ≤ k then 1 else 0) + (if k ≤ l then 1 else 0)) := by
  rw [kingmanTimeMoment]
  split_ifs with h1 h2 h3 h4 h5 <;> first | omega | (subst_vars; ring)

private theorem blockCountMoment_of_le {n k l i j : ℕ} (h : k ≤ l) :
    blockCountMoment n k l i j =
      joinPair (n - l) (n - k) (fun b => (b.count j : ℝ)) (fun b => (b.count i : ℝ))
        (List.replicate n 1) := by
  rw [blockCountMoment]
  split_ifs with hlk
  · have : l = k := le_antisymm hlk h
    subst this
    simp only [joinPair, Nat.sub_self, Function.iterate_zero, id]
    exact congrFun (congrArg (fun F => joinStep^[n - l] F) (funext fun y => mul_comm _ _)) _
  · rfl

/-- **`fuTopologyCov` through level moments.** -/
theorem fuTopologyCov_eq_levelMoment {n i j : ℕ} (hi : 1 ≤ i) (hin : i < n) (hj : 1 ≤ j)
    (hjn : j < n) :
    fuTopologyCov n i j =
      ∑ k ∈ Icc 2 n, ((k.choose 2 : ℕ) : ℝ)⁻¹ * levelMoment n k i j +
        ∑ k ∈ Icc 2 n, ((k.choose 2 : ℕ) : ℝ)⁻¹ * levelMoment n k j i - 2 / i * (2 / j) := by
  have hmean : ∀ i, 1 ≤ i → i < n → ∑ k ∈ Icc 2 n, blockCountMean n k i *
      ((k.choose 2 : ℕ) : ℝ)⁻¹ = 2 / i := by
    intro i hi hin
    rw [← sum_blockCount_mul_inv_choose_two hi hin]
    refine sum_congr rfl fun k hk => ?_
    rw [blockCountMean, joinStep_iterate_count (mem_Icc.1 hk).1 (mem_Icc.1 hk).2 hi hin]
  rw [fuTopologyCov, hmean i hi hin, hmean j hj hjn]
  congr 1
  simp only [kingmanTimeMoment_eq, mul_add, mul_ite, mul_one, mul_zero, sum_add_distrib]
  congr 1
  · refine sum_congr rfl fun k hk => ?_
    rw [levelMoment, mul_sum, ← sum_filter]
    have hf : (Icc 2 n).filter (· ≤ k) = Icc 2 k := by
      ext l; simp only [mem_filter, mem_Icc]; have := (mem_Icc.1 hk).2; omega
    rw [hf]
    refine sum_congr rfl fun l hl => ?_
    simp only [blockCountMoment, (mem_Icc.1 hl).2, ↓reduceIte]
    ring
  · rw [sum_comm]
    refine sum_congr rfl fun l hl => ?_
    rw [levelMoment, mul_sum, ← sum_filter]
    have hf : (Icc 2 n).filter (· ≤ l) = Icc 2 l := by
      ext k; simp only [mem_filter, mem_Icc]; have := (mem_Icc.1 hl).2; omega
    rw [hf]
    refine sum_congr rfl fun k hk => ?_
    rw [blockCountMoment_of_le (mem_Icc.1 hk).2]
    ring

/-! ### Harmonic sums of binomial ratios -/

/-- The harmonic number `H_m = ∑_{k=1}^{m} 1/k`. -/
noncomputable def harm (m : ℕ) : ℝ := ∑ k ∈ Icc 1 m, (k : ℝ)⁻¹

theorem harm_succ (m : ℕ) : harm (m + 1) = harm m + ((m : ℝ) + 1)⁻¹ := by
  rw [harm, harm, sum_Icc_succ_top (by omega)]
  push_cast; ring

theorem tajimaA1_succ_eq_harm (m : ℕ) : tajimaA1 (m + 1) = harm m := by
  rw [tajimaA1, harm]
  congr 1

theorem sum_choose_sub_div (N : ℕ) : ∀ r, ∑ k ∈ Icc 1 N, ((N - k).choose r : ℝ) / k =
    (N.choose r : ℝ) * (harm N - harm r) := by
  induction N with
  | zero => intro r; rcases r with _ | r <;> simp [harm]
  | succ N ih =>
    intro r
    rcases r with _ | r
    · simp [harm, div_eq_mul_inv]
    rw [sum_Icc_succ_top (by omega), Nat.sub_self, Nat.choose_zero_succ, Nat.cast_zero, zero_div,
      add_zero]
    have hstep : ∀ k ∈ Icc 1 N, ((N + 1 - k).choose (r + 1) : ℝ) / k =
        ((N - k).choose r : ℝ) / k + ((N - k).choose (r + 1) : ℝ) / k := by
      intro k hk
      rw [show N + 1 - k = (N - k) + 1 by have := (mem_Icc.1 hk).2; omega,
        Nat.choose_succ_succ', Nat.cast_add, add_div]
    rw [sum_congr rfl hstep, sum_add_distrib, ih r, ih (r + 1), harm_succ, harm_succ,
      Nat.choose_succ_succ', Nat.cast_add]
    have hk : ((N + 1).choose (r + 1) : ℝ) * (r + 1) = ((N : ℝ) + 1) * (N.choose r : ℝ) := by
      have := Nat.add_one_mul_choose_eq N r
      exact_mod_cast this.symm
    rw [Nat.choose_succ_succ', Nat.cast_add] at hk
    have h1 : ((r : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((N : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    linear_combination (-1 : ℝ) * hk

theorem sum_Icc_two_choose_sub_div {n : ℕ} (hn : 1 ≤ n) (r : ℕ) :
    ∑ k ∈ Icc 2 n, ((n - k).choose r : ℝ) / k =
      (n.choose r : ℝ) * (harm n - harm r) - ((n - 1).choose r : ℝ) := by
  rw [← sum_choose_sub_div n r, ← add_sum_Ioc_eq_sum_Icc hn,
    show Ioc 1 n = Icc 2 n by ext; simp only [mem_Ioc, mem_Icc]; omega]
  simp

theorem sum_Icc_two_choose_sub_div_pred {n : ℕ} (hn : 1 ≤ n) (r : ℕ) :
    ∑ k ∈ Icc 2 n, ((n - k).choose r : ℝ) / ((k : ℝ) - 1) =
      ((n - 1).choose r : ℝ) * (harm (n - 1) - harm r) := by
  rw [← sum_choose_sub_div (n - 1) r]
  refine sum_nbij' (· - 1) (· + 1) ?_ ?_ ?_ ?_ ?_ <;> intro k hk <;>
    simp only [mem_Icc] at hk ⊢
  · omega
  · omega
  · omega
  · omega
  · rw [show n - 1 - (k - 1) = n - k by omega, Nat.cast_sub (by omega : 1 ≤ k)]
    simp

/-- `C(n-i-1, k-2) (n-1) C(n-2, i-1) = (k-1) C(n-k, i-1) C(n-1, k-1)`. -/
theorem choose_mul_choose_eq_conv {n k i : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (hi : 1 ≤ i)
    (hin : i < n) :
    (n - i - 1).choose (k - 2) * ((n - 1) * (n - 2).choose (i - 1)) =
      (k - 1) * ((n - k).choose (i - 1) * (n - 1).choose (k - 1)) := by
  rcases Nat.lt_or_ge (n + 1) (k + i) with h | h
  · rw [Nat.choose_eq_zero_of_lt (by omega : n - i - 1 < k - 2),
      Nat.choose_eq_zero_of_lt (by omega : n - k < i - 1)]
    simp
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 2 := ⟨k - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, i = b + 1 := ⟨i - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, n = a + b + c + 2 := ⟨n - a - b - 2, by omega⟩
  simp only [show a + b + c + 2 - (b + 1) - 1 = a + c by omega, Nat.add_sub_cancel,
    show a + b + c + 2 - 1 = a + b + c + 1 by omega, show a + b + c + 2 - 2 = a + b + c by omega,
    show a + b + c + 2 - (a + 2) = b + c by omega, show a + 2 - 1 = a + 1 by omega]
  have h1 := Nat.choose_mul (n := a + b + c) (k := a + c) (s := a) (by omega)
  rw [show a + b + c - a = b + c by omega, show a + c - a = c by omega,
    Nat.choose_symm_of_eq_add (show a + b + c = (a + c) + b by ring),
    ← (Nat.choose_symm_add : (b + c).choose b = (b + c).choose c)] at h1
  have h2 := Nat.add_one_mul_choose_eq (a + b + c) a
  calc (a + c).choose a * ((a + b + c + 1) * (a + b + c).choose b)
      = (a + b + c + 1) * ((a + b + c).choose b * (a + c).choose a) := by ring
    _ = (a + b + c + 1) * ((a + b + c).choose a * (b + c).choose b) := by rw [h1]
    _ = (a + 1) * ((b + c).choose b * (a + b + c + 1).choose (a + 1)) := by
        rw [← mul_assoc, h2]; ring

/-- `C(j, k-1) C(n-1, i-1) = C(n-k, i-1) C(n-1, k-1)` when `i + j = n`. -/
theorem choose_mul_choose_eq_conv' {n k i j : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (hi : 1 ≤ i)
    (hij : i + j = n) :
    j.choose (k - 1) * (n - 1).choose (i - 1) =
      (n - k).choose (i - 1) * (n - 1).choose (k - 1) := by
  rcases Nat.lt_or_ge j (k - 1) with h | h
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega : n - k < i - 1)]
    simp
  have h1 := Nat.choose_mul (n := n - 1) (k := j) (s := k - 1) h
  rw [show n - 1 - (k - 1) = n - k by omega,
    Nat.choose_symm_of_eq_add (show n - k = (j - (k - 1)) + (i - 1) by omega),
    Nat.choose_symm_of_eq_add (show n - 1 = j + (i - 1) by omega)] at h1
  rw [mul_comm, h1, mul_comm]

/-- **The first harmonic sum**: `∑_{k=2}^{n} C(n-i-1, k-2) / (C(n-1, k-1) C(k, 2)) = β_n(i)`. -/
theorem sum_choose_div_choose_mul_inv_choose_two {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    ∑ k ∈ Icc 2 n, ((k.choose 2 : ℕ) : ℝ)⁻¹ * ((n - i - 1).choose (k - 2) : ℝ) /
      ((n - 1).choose (k - 1) : ℝ) = fuBeta n i := by
  have hD : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) * ((n - 2).choose (i - 1) : ℝ) := by
    have : 0 < (n - 2).choose (i - 1) := Nat.choose_pos (by omega)
    have : 0 < n - 1 := by omega
    positivity
  have hterm : ∀ k ∈ Icc 2 n, ((k.choose 2 : ℕ) : ℝ)⁻¹ * ((n - i - 1).choose (k - 2) : ℝ) /
      ((n - 1).choose (k - 1) : ℝ) =
      2 / (((n - 1 : ℕ) : ℝ) * ((n - 2).choose (i - 1) : ℝ)) *
        (((n - k).choose (i - 1) : ℝ) / k) := by
    intro k hk
    obtain ⟨hk2, hkn⟩ := mem_Icc.1 hk
    have hc : (0 : ℝ) < ((n - 1).choose (k - 1) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    have hconv : ((n - i - 1).choose (k - 2) : ℝ) *
        (((n - 1 : ℕ) : ℝ) * ((n - 2).choose (i - 1) : ℝ)) =
        ((k : ℝ) - 1) * (((n - k).choose (i - 1) : ℝ) * ((n - 1).choose (k - 1) : ℝ)) := by
      have := choose_mul_choose_eq_conv hk2 hkn hi hin
      rw [show (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) by rw [Nat.cast_sub (by omega)]; simp]
      exact_mod_cast this
    have hX : ((n - i - 1).choose (k - 2) : ℝ) =
        ((k : ℝ) - 1) * (((n - k).choose (i - 1) : ℝ) * ((n - 1).choose (k - 1) : ℝ)) /
          (((n - 1 : ℕ) : ℝ) * ((n - 2).choose (i - 1) : ℝ)) := by
      rw [eq_div_iff hD.ne']; exact hconv
    rw [Nat.cast_choose_two, hX]
    have hk1 : (k : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      linarith
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    field_simp
  rw [sum_congr rfl hterm, ← mul_sum, sum_Icc_two_choose_sub_div (by omega), fuBeta,
    tajimaA1_succ_eq_harm, show i = (i - 1) + 1 by omega, tajimaA1_succ_eq_harm,
    show i - 1 + 1 = i by omega]
  have e1 : ((n - 2).choose (i - 1) : ℝ) * ((n - 1 : ℕ) : ℝ) =
      ((n - 1).choose (i - 1) : ℝ) * ((n : ℝ) - i) := by
    have := Nat.choose_mul_succ_eq (n - 2) (i - 1)
    rw [show n - 2 + 1 = n - 1 by omega, show n - 1 - (i - 1) = n - i by omega] at this
    rw [show (n : ℝ) - i = ((n - i : ℕ) : ℝ) by rw [Nat.cast_sub hin.le]]
    exact_mod_cast this
  have e2 : ((n - 1).choose (i - 1) : ℝ) * (n : ℝ) =
      (n.choose (i - 1) : ℝ) * ((n : ℝ) - i + 1) := by
    have := Nat.choose_mul_succ_eq (n - 1) (i - 1)
    rw [show n - 1 + 1 = n by omega, show n - (i - 1) = n - i + 1 by omega] at this
    rw [show (n : ℝ) - i + 1 = ((n - i + 1 : ℕ) : ℝ) by push_cast [Nat.cast_sub hin.le]; ring]
    exact_mod_cast this
  have hni : (0 : ℝ) < (n : ℝ) - i := by
    have : (i : ℝ) < n := by exact_mod_cast hin
    linarith
  have hc1 : (0 : ℝ) < ((n - 1).choose (i - 1) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  rw [mul_comm (((n - 1 : ℕ) : ℝ)), e1]
  have hcn : (n.choose (i - 1) : ℝ) = ((n - 1).choose (i - 1) : ℝ) * n / ((n : ℝ) - i + 1) := by
    rw [e2, mul_div_assoc, div_self (by linarith), mul_one]
  rw [hcn]
  field_simp

/-- **The second harmonic sum** (`i + j = n`):
`∑_{k=2}^{n} C(j, k-1) / (C(n-1, k-1) C(k, 2)) 
= 2 (H_{n-1} - H_{i-1}) - 2 n / (n-i+1) (H_n - H_{i-1}) + 2`. -/
theorem sum_choose_div_choose_mul_inv_choose_two' {n i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hij : i + j = n) :
    ∑ k ∈ Icc 2 n, ((k.choose 2 : ℕ) : ℝ)⁻¹ * (j.choose (k - 1) : ℝ) /
      ((n - 1).choose (k - 1) : ℝ) =
      2 * (harm (n - 1) - harm (i - 1)) - 2 * n / ((n : ℝ) - i + 1) * (harm n - harm (i - 1)) +
        2 := by
  have hc1 : (0 : ℝ) < ((n - 1).choose (i - 1) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hterm : ∀ k ∈ Icc 2 n, ((k.choose 2 : ℕ) : ℝ)⁻¹ * (j.choose (k - 1) : ℝ) /
      ((n - 1).choose (k - 1) : ℝ) = 2 / ((n - 1).choose (i - 1) : ℝ) *
        (((n - k).choose (i - 1) : ℝ) / ((k : ℝ) - 1) - ((n - k).choose (i - 1) : ℝ) / k) := by
    intro k hk
    obtain ⟨hk2, hkn⟩ := mem_Icc.1 hk
    have hc : (0 : ℝ) < ((n - 1).choose (k - 1) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    have hX : (j.choose (k - 1) : ℝ) = ((n - k).choose (i - 1) : ℝ) *
        ((n - 1).choose (k - 1) : ℝ) / ((n - 1).choose (i - 1) : ℝ) := by
      rw [eq_div_iff hc1.ne']
      exact_mod_cast choose_mul_choose_eq_conv' hk2 hkn hi hij
    rw [Nat.cast_choose_two, hX]
    have hk1 : (k : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      linarith
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [sum_congr rfl hterm, ← mul_sum, sum_sub_distrib, sum_Icc_two_choose_sub_div_pred (by omega),
    sum_Icc_two_choose_sub_div (by omega)]
  have hin : i < n := by omega
  have e2 : ((n - 1).choose (i - 1) : ℝ) * (n : ℝ) =
      (n.choose (i - 1) : ℝ) * ((n : ℝ) - i + 1) := by
    have := Nat.choose_mul_succ_eq (n - 1) (i - 1)
    rw [show n - 1 + 1 = n by omega, show n - (i - 1) = n - i + 1 by omega] at this
    rw [show (n : ℝ) - i + 1 = ((n - i + 1 : ℕ) : ℝ) by push_cast [Nat.cast_sub hin.le]; ring]
    exact_mod_cast this
  have hni : (0 : ℝ) < (n : ℝ) - i + 1 := by
    have : (i : ℝ) < n := by exact_mod_cast hin
    linarith
  have hcn : (n.choose (i - 1) : ℝ) = ((n - 1).choose (i - 1) : ℝ) * n / ((n : ℝ) - i + 1) := by
    rw [e2, mul_div_assoc, div_self hni.ne', mul_one]
  rw [hcn]
  field_simp
  ring

theorem vandermonde_range (a b r : ℕ) :
    ∑ p ∈ range (r + 1), (a.choose p : ℝ) * (b.choose (r - p) : ℝ) = ((a + b).choose r : ℝ) := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  push_cast
  rfl

theorem card_comps_of_pos {y r : ℕ} (hy : 1 ≤ y) (hr : 1 ≤ r) :
    ((comps y r).card : ℝ) = ((y - 1).choose (r - 1) : ℝ) := card_comps hr hy

theorem card_comps_zero_left {r : ℕ} (hr : 1 ≤ r) : ((comps 0 r).card : ℝ) = 0 := by
  rw [card_comps_eq]; simp [show r ≠ 0 by omega]

theorem card_comps_zero_right {y : ℕ} (hy : 1 ≤ y) : ((comps y 0).card : ℝ) = 0 := by
  rw [card_comps_eq]; simp [show y ≠ 0 by omega]

theorem sum_cladeWeight_mul_choose (k : ℕ) (F : ℕ → ℝ) :
    ∑ m ∈ range (k + 1), cladeWeight k m * (k.choose m : ℝ) * F m = ∑ m ∈ Ico 1 k, 2 / m * F m := by
  symm
  refine sum_subset_zero_on_sdiff (fun m hm => by
    simp only [mem_Ico] at hm; simp only [mem_range]; omega) (fun m hm => ?_) (fun m hm => ?_)
  · simp only [mem_sdiff, mem_range, mem_Ico] at hm
    rw [cladeWeight_of_not (by omega)]; ring
  · obtain ⟨h1, h2⟩ := mem_Ico.1 hm
    have hc : (0 : ℝ) < (k.choose m : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
    rw [cladeWeight_of h1 h2]
    field_simp

/-- The `m`-sum for blocks nested in the size-`j` set. -/
theorem sum_nested {n k i j : ℕ} (hk : 2 ≤ k) (hjn : j < n) :
    ∑ m ∈ Ico 1 k, (if i ≤ j then ((comps (j - i) (m - 1)).card : ℝ) else 0) *
        ((comps (n - j) (k - m)).card : ℝ) =
      (if i < j then ((n - i - 1).choose (k - 2) : ℝ) - ((n - i - 2).choose (k - 2) : ℝ) else 0) +
        (if i = j then ((n - i - 1).choose (k - 2) : ℝ) else 0) := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp only [h.le, ↓reduceIte, h, h.ne]
    rw [sum_Ico_eq_sum_range, show k - 1 = (k - 2) + 1 by omega, sum_range_succ']
    simp only [add_zero, card_comps_zero_right (show 1 ≤ j - i by omega),
      zero_mul, add_zero]
    have hterm : ∀ q ∈ range (k - 2), ((comps (j - i) (1 + (q + 1) - 1)).card : ℝ) *
        ((comps (n - j) (k - (1 + (q + 1)))).card : ℝ) =
        ((j - i - 1).choose q : ℝ) * ((n - j - 1).choose (k - 3 - q) : ℝ) := by
      intro q hq
      rw [mem_range] at hq
      rw [card_comps_of_pos (by omega) (by omega), card_comps_of_pos (by omega) (by omega),
        show 1 + (q + 1) - 1 - 1 = q by omega, show k - (1 + (q + 1)) - 1 = k - 3 - q by omega]
    rw [sum_congr rfl hterm]
    rcases Nat.eq_or_lt_of_le hk with rfl | hk3
    · simp
    rw [show k - 2 = (k - 3) + 1 by omega, vandermonde_range,
      show j - i - 1 + (n - j - 1) = n - i - 2 by omega,
      show n - i - 1 = (n - i - 2) + 1 by omega, show k - 3 + 1 = k - 2 by omega,
      show k - 2 = (k - 3) + 1 by omega, Nat.choose_succ_succ', Nat.cast_add]
    ring
  · simp only [le_refl, ↓reduceIte, lt_irrefl, Nat.sub_self, zero_add]
    rw [sum_eq_single_of_mem 1 (by simp only [mem_Ico]; omega)]
    · rw [Nat.sub_self, card_comps_eq]
      simp only [↓reduceIte, one_mul]
      rw [card_comps_of_pos (by omega) (by omega), show n - i - 1 = n - i - 1 by rfl,
        show k - 1 - 1 = k - 2 by omega]
    · intro m hm hm1
      rw [card_comps_zero_left (by simp only [mem_Ico] at hm; omega)]
      ring
  · simp only [show ¬ i ≤ j by omega, ↓reduceIte, zero_mul, sum_const_zero,
      show ¬ i < j by omega, show i ≠ j by omega, add_zero]

/-- The `m`-sum for blocks disjoint from the size-`j` set. -/
theorem sum_disjoint {n k i j : ℕ} (hk : 2 ≤ k) (hj : 1 ≤ j) (hjn : j < n) :
    ∑ m ∈ Ico 1 k, 1 / (m : ℝ) * ((comps j m).card : ℝ) * ((k - m : ℕ) *
        (if i ≤ n - j then ((comps (n - j - i) (k - m - 1)).card : ℝ) else 0)) =
      ((if i + j < n then ((n - i - j - 1 : ℕ) : ℝ) *
            (((n - i - 1).choose (k - 2) : ℝ) - ((n - i - 2).choose (k - 2) : ℝ)) +
          2 * ((n - i - 1).choose (k - 2) : ℝ) - k * ((n - i - j - 1).choose (k - 2) : ℝ)
        else 0) + (if i + j = n then (j.choose (k - 1) : ℝ) else 0)) / j := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  rcases lt_trichotomy (i + j) n with h | h | h
  · simp only [show i ≤ n - j by omega, ↓reduceIte, h, h.ne, add_zero]
    set M := n - i - j - 1 with hM
    -- rewrite the summand
    have hterm : ∀ m ∈ Ico 1 k, 1 / (m : ℝ) * ((comps j m).card : ℝ) * ((k - m : ℕ) *
        ((comps (n - j - i) (k - m - 1)).card : ℝ)) =
        (1 / j) * ((j.choose m : ℝ) * ((k - m : ℕ) : ℝ) *
          (if k - m - 1 = 0 then 0 else (M.choose (k - 2 - m) : ℝ))) := by
      intro m hm
      obtain ⟨hm1, hmk⟩ := mem_Ico.1 hm
      have hjm : (j : ℝ) * ((j - 1).choose (m - 1) : ℝ) = (j.choose m : ℝ) * m := by
        have := Nat.add_one_mul_choose_eq (j - 1) (m - 1)
        rw [show j - 1 + 1 = j by omega, show m - 1 + 1 = m by omega] at this
        exact_mod_cast this
      have hm0 : (m : ℝ) ≠ 0 := by
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
        linarith
      rw [card_comps_of_pos hj hm1]
      split_ifs with hz
      · rw [hz, card_comps_zero_right (by omega)]; ring
      · rw [card_comps_of_pos (by omega) (by omega), show n - j - i - 1 = M by omega,
          show k - m - 1 - 1 = k - 2 - m by omega]
        field_simp
        linear_combination (((k - m : ℕ) : ℝ) * (M.choose (k - 2 - m) : ℝ)) * hjm
    rw [sum_congr rfl hterm, ← mul_sum, one_div_mul_eq_div]
    congr 1
    -- extend to `m = 0`
    have hext : ∑ m ∈ range (k - 1), (j.choose m : ℝ) * ((k - m : ℕ) : ℝ) *
        (M.choose (k - 2 - m) : ℝ) = ∑ m ∈ Ico 1 k, (j.choose m : ℝ) * ((k - m : ℕ) : ℝ) *
          (if k - m - 1 = 0 then 0 else (M.choose (k - 2 - m) : ℝ)) +
        k * (M.choose (k - 2) : ℝ) := by
      rw [show k - 1 = (k - 2) + 1 by omega, sum_range_succ', sum_Ico_eq_sum_range,
        show k - 1 = (k - 2) + 1 by omega, sum_range_succ]
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
        show k - (1 + (k - 2)) - 1 = 0 by omega, ↓reduceIte, mul_zero, add_zero]
      congr 1
      refine sum_congr rfl fun q hq => ?_
      rw [mem_range] at hq
      simp only [show ¬ (k - (1 + q) - 1 = 0) by omega, ↓reduceIte]
      rw [show 1 + q = q + 1 by ring]
    have hsplit : ∀ m ∈ range (k - 1), (j.choose m : ℝ) * ((k - m : ℕ) : ℝ) *
        (M.choose (k - 2 - m) : ℝ) = 2 * ((j.choose m : ℝ) * (M.choose (k - 2 - m) : ℝ)) +
          ((j.choose m : ℝ) * (((k - 2 - m : ℕ) : ℝ) * (M.choose (k - 2 - m) : ℝ))) := by
      intro m hm
      rw [mem_range] at hm
      rw [show ((k - m : ℕ) : ℝ) = ((k - 2 - m : ℕ) : ℝ) + 2 by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring]
      ring
    have hvand2 : ∑ m ∈ range (k - 1), (j.choose m : ℝ) * (M.choose (k - 2 - m) : ℝ) =
        ((n - i - 1).choose (k - 2) : ℝ) := by
      rw [show k - 1 = (k - 2) + 1 by omega, vandermonde_range, show j + M = n - i - 1 by omega]
    have hvand1 : ∑ m ∈ range (k - 1), (j.choose m : ℝ) * (((k - 2 - m : ℕ) : ℝ) *
        (M.choose (k - 2 - m) : ℝ)) = (M : ℝ) *
          (((n - i - 1).choose (k - 2) : ℝ) - ((n - i - 2).choose (k - 2) : ℝ)) := by
      have hr : ∀ m ∈ range (k - 1), (j.choose m : ℝ) * (((k - 2 - m : ℕ) : ℝ) *
          (M.choose (k - 2 - m) : ℝ)) =
          (M : ℝ) * (if m = k - 2 then 0 else
            (j.choose m : ℝ) * ((M - 1).choose (k - 3 - m) : ℝ)) := by
        intro m hm
        rw [mem_range] at hm
        split_ifs with hmk
        · rw [hmk, Nat.sub_self]; simp
        · rcases Nat.eq_zero_or_pos M with hM0 | hM0
          · rw [hM0, Nat.choose_eq_zero_of_lt (by omega : 0 < k - 2 - m)]; simp
          have := Nat.add_one_mul_choose_eq (M - 1) (k - 3 - m)
          rw [show M - 1 + 1 = M by omega, show k - 3 - m + 1 = k - 2 - m by omega] at this
          have h' : (M : ℝ) * ((M - 1).choose (k - 3 - m) : ℝ) =
              (M.choose (k - 2 - m) : ℝ) * ((k - 2 - m : ℕ) : ℝ) := by exact_mod_cast this
          linear_combination (j.choose m : ℝ) * h'.symm
      rw [sum_congr rfl hr, ← mul_sum]
      rcases Nat.eq_zero_or_pos M with hM0 | hM0
      · rw [hM0]; simp
      congr 1
      rcases Nat.eq_or_lt_of_le hk with rfl | hk3
      · simp
      rw [show k - 1 = (k - 2) + 1 by omega, sum_range_succ]
      simp only [↓reduceIte, add_zero]
      rw [sum_congr rfl (g := fun m => (j.choose m : ℝ) * ((M - 1).choose (k - 3 - m) : ℝ))
          fun m hm => by
            simp only [show m ≠ k - 2 by rw [mem_range] at hm; omega, ↓reduceIte],
        show k - 2 = (k - 3) + 1 by omega, vandermonde_range,
        show j + (M - 1) = n - i - 2 by omega, show n - i - 1 = (n - i - 2) + 1 by omega,
        Nat.choose_succ_succ', Nat.cast_add]
      ring
    have hr2 : ∑ m ∈ range (k - 1), (j.choose m : ℝ) * ((k - m : ℕ) : ℝ) *
        (M.choose (k - 2 - m) : ℝ) = 2 * ((n - i - 1).choose (k - 2) : ℝ) + (M : ℝ) *
          (((n - i - 1).choose (k - 2) : ℝ) - ((n - i - 2).choose (k - 2) : ℝ)) := by
      rw [sum_congr rfl hsplit, sum_add_distrib, ← mul_sum, hvand2, hvand1]
    linear_combination hr2 - hext
  · have hif : ∀ m, (if i ≤ n - j then ((comps (n - j - i) (k - m - 1)).card : ℝ) else 0) =
        ((comps 0 (k - m - 1)).card : ℝ) := fun m => by
      simp only [show i ≤ n - j by omega, ↓reduceIte, show n - j - i = 0 by omega]
    simp only [hif, h, lt_irrefl, ↓reduceIte, zero_add]
    rw [sum_eq_single_of_mem (k - 1) (by simp only [mem_Ico]; omega)]
    · rw [show k - (k - 1) - 1 = 0 by omega, show k - (k - 1) = 1 by omega, card_comps_eq 0 0,
        card_comps_of_pos hj (by omega), show k - 1 - 1 = k - 2 by omega]
      simp only [↓reduceIte, Nat.cast_one, mul_one]
      have := Nat.add_one_mul_choose_eq (j - 1) (k - 2)
      rw [show j - 1 + 1 = j by omega, show k - 2 + 1 = k - 1 by omega] at this
      have h' : (j : ℝ) * ((j - 1).choose (k - 2) : ℝ) =
          (j.choose (k - 1) : ℝ) * ((k - 1 : ℕ) : ℝ) := by exact_mod_cast this
      have hk1 : ((k - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show k - 1 ≠ 0 by omega)
      have hC : (j.choose (k - 1) : ℝ) = j * ((j - 1).choose (k - 2) : ℝ) / ((k - 1 : ℕ) : ℝ) := by
        rw [eq_div_iff hk1, h']
      rw [hC]
      field_simp
    · intro m hm hmk
      rw [card_comps_zero_left (by simp only [mem_Ico] at hm; omega)]
      simp
  · simp only [show ¬ i ≤ n - j by omega, ↓reduceIte, mul_zero, sum_const_zero,
      show ¬ (i + j < n) by omega, show i + j ≠ n by omega, add_zero, zero_div]

/-! ### The level moments in closed form -/

/-- Coefficients of the four binomial-ratio sums in the level moment. -/
noncomputable def coefA (n i j : ℕ) : ℝ :=
  (if i < j then 1 else 0) + (if i = j then 1 else 0) +
    (if i + j < n then (((n - i - j - 1 : ℕ) : ℝ) + 2) / j else 0)

noncomputable def coefB (n i j : ℕ) : ℝ :=
  -(if i < j then 1 else 0) - (if i + j < n then ((n - i - j - 1 : ℕ) : ℝ) / j else 0)

noncomputable def coefC (n i j : ℕ) : ℝ := -(if i + j < n then 1 / (j : ℝ) else 0)

noncomputable def coefD (n i j : ℕ) : ℝ := if i + j = n then 1 / (j : ℝ) else 0

theorem levelMoment_closed {n k i j : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hjn : j < n) :
    levelMoment n k i j * ((n - 1).choose (k - 1) : ℝ) =
      2 * (coefA n i j * ((n - i - 1).choose (k - 2) : ℝ) +
        coefB n i j * ((n - i - 2).choose (k - 2) : ℝ) +
        coefC n i j * (k * ((n - (i + j) - 1).choose (k - 2) : ℝ)) +
        coefD n i j * (j.choose (k - 1) : ℝ)) := by
  rw [levelMoment_eq n k i j hk hkn, sum_comps_count_mul_cladeStat n k i j hi hjn.le,
    sum_cladeWeight_mul_choose]
  have hsplit : ∀ m ∈ Ico 1 k, 2 / (m : ℝ) *
      ((m : ℝ) * (if i ≤ j then ((comps (j - i) (m - 1)).card : ℝ) else 0) *
          ((comps (n - j) (k - m)).card : ℝ) +
        ((comps j m).card : ℝ) * ((k - m : ℕ) *
          (if i ≤ n - j then ((comps (n - j - i) (k - m - 1)).card : ℝ) else 0))) =
      2 * ((if i ≤ j then ((comps (j - i) (m - 1)).card : ℝ) else 0) *
          ((comps (n - j) (k - m)).card : ℝ)) +
      2 * (1 / (m : ℝ) * ((comps j m).card : ℝ) * ((k - m : ℕ) *
          (if i ≤ n - j then ((comps (n - j - i) (k - m - 1)).card : ℝ) else 0))) := by
    intro m hm
    have hm0 : (m : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Ico.1 hm).1
      linarith
    field_simp
  rw [sum_congr rfl hsplit, sum_add_distrib, ← mul_sum, ← mul_sum, sum_nested hk hjn,
    sum_disjoint hk hj hjn, coefA, coefB, coefC, coefD,
    show n - (i + j) - 1 = n - i - j - 1 by omega]
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  split_ifs <;> first | omega | (field_simp; ring)

/-- The closed form of `∑_k T̄_k E[c_{k,i} R̃_j]` (Fu's covariance before symmetrization). -/
noncomputable def fuHalfCov (n i j : ℕ) : ℝ :=
  2 * (coefA n i j * fuBeta n i +
    coefB n i j * (if i + 1 < n then fuBeta n (i + 1) else 0) +
    coefC n i j * (if i + j < n then 2 / ((i : ℝ) + j) else 0) +
    coefD n i j * (2 * (harm (n - 1) - harm (i - 1)) -
      2 * n / ((n : ℝ) - i + 1) * (harm n - harm (i - 1)) + 2))

theorem sum_levelMoment {n i j : ℕ} (hi : 1 ≤ i) (hin : i < n) (hj : 1 ≤ j) (hjn : j < n) :
    ∑ k ∈ Icc 2 n, ((k.choose 2 : ℕ) : ℝ)⁻¹ * levelMoment n k i j = fuHalfCov n i j := by
  have hterm : ∀ k ∈ Icc 2 n, ((k.choose 2 : ℕ) : ℝ)⁻¹ * levelMoment n k i j =
      2 * (coefA n i j * (((k.choose 2 : ℕ) : ℝ)⁻¹ * ((n - i - 1).choose (k - 2) : ℝ) /
          ((n - 1).choose (k - 1) : ℝ)) +
        coefB n i j * (((k.choose 2 : ℕ) : ℝ)⁻¹ * ((n - i - 2).choose (k - 2) : ℝ) /
          ((n - 1).choose (k - 1) : ℝ)) +
        coefC n i j * (k * ((n - (i + j) - 1).choose (k - 2) : ℝ) /
          ((n - 1).choose (k - 1) : ℝ) * ((k.choose 2 : ℕ) : ℝ)⁻¹) +
        coefD n i j * (((k.choose 2 : ℕ) : ℝ)⁻¹ * (j.choose (k - 1) : ℝ) /
          ((n - 1).choose (k - 1) : ℝ))) := by
    intro k hk
    obtain ⟨hk2, hkn⟩ := mem_Icc.1 hk
    have hc : (0 : ℝ) < ((n - 1).choose (k - 1) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    have h := levelMoment_closed hk2 hkn hi hj hjn
    rw [← eq_div_iff hc.ne'] at h
    rw [h]
    field_simp
  rw [sum_congr rfl hterm, ← mul_sum, sum_add_distrib, sum_add_distrib, sum_add_distrib,
    ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum, sum_choose_div_choose_mul_inv_choose_two hi hin,
    fuHalfCov]
  congr 2
  · congr 1
    · congr 1
      split_ifs with h1
      · rw [show n - i - 2 = n - (i + 1) - 1 by omega,
          sum_choose_div_choose_mul_inv_choose_two (by omega) h1]
      · have : coefB n i j = 0 := by
          rw [coefB]; split_ifs <;> first | omega | simp
        rw [this]; simp
    · split_ifs with h1
      · rw [sum_blockCount_mul_inv_choose_two (by omega) h1]
        push_cast; ring
      · have : coefC n i j = 0 := by rw [coefC]; simp [h1]
        rw [this]; simp
  · by_cases h1 : i + j = n
    · rw [sum_choose_div_choose_mul_inv_choose_two' hi hj h1]
    · have : coefD n i j = 0 := by rw [coefD]; simp [h1]
      rw [this]; simp

/-! ### Fu's closed form -/

theorem tajimaA1_succ_of_pos {i : ℕ} (hi : 1 ≤ i) : tajimaA1 (i + 1) = tajimaA1 i + (i : ℝ)⁻¹ := by
  rw [tajimaA1, tajimaA1, sum_Ico_succ_top hi]

theorem tajimaA1_eq_harm {m : ℕ} (hm : 1 ≤ m) : tajimaA1 m = harm (m - 1) := by
  rw [← tajimaA1_succ_eq_harm, Nat.sub_add_cancel hm]

/-- Fu's `β` satisfies `(n - i + 1) β_n(i) - (n - i - 1) β_n(i + 1) = 2 / i`. -/
theorem fuBeta_rec {n i : ℕ} (hi : 1 ≤ i) (hin : i + 1 < n) :
    ((n : ℝ) - i + 1) * fuBeta n i - ((n : ℝ) - i - 1) * fuBeta n (i + 1) = 2 / i := by
  rw [fuBeta, fuBeta, tajimaA1_succ_of_pos hi]
  have h1 : (0 : ℝ) < (n : ℝ) - (i + 1) := by
    have : ((i + 1 : ℕ) : ℝ) < n := by exact_mod_cast hin
    push_cast at this; linarith
  have h2 : (0 : ℝ) < (n : ℝ) - (i + 1) + 1 := by linarith
  have h3 : (0 : ℝ) < (n : ℝ) - i := by linarith
  have h4 : (0 : ℝ) < (n : ℝ) - i + 1 := by linarith
  have h5 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  push_cast
  field_simp
  ring

private theorem cast_sub_sub_sub {n i j : ℕ} (h : i + j < n) :
    ((n - i - j - 1 : ℕ) : ℝ) = (n : ℝ) - i - j - 1 := by
  rw [Nat.cast_sub (show 1 ≤ n - i - j by omega), Nat.cast_sub (show j ≤ n - i by omega),
    Nat.cast_sub (show i ≤ n by omega)]
  simp

/-- **Fu's closed form from the half covariances**, for `1 ≤ i ≤ j < n`. -/
theorem fuHalfCov_add_fuHalfCov {n i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hjn : j < n) :
    fuHalfCov n i j + fuHalfCov n j i - 2 / i * (2 / j) = 4 * fuSigma n i j := by
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 1 ≤ j by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · -- diagonal
    rcases lt_trichotomy (i + i) n with h | h | h
    · have hr := fuBeta_rec hi (show i + 1 < n by omega)
      simp only [fuHalfCov, coefA, coefB, coefC, coefD, fuSigma, lt_irrefl, h,
        show i + 1 < n by omega, show 2 * i < n by omega, show i + i ≠ n by omega, ↓reduceIte,
        cast_sub_sub_sub h]
      set u := fuBeta n i
      set v := fuBeta n (i + 1)
      have hne : (n : ℝ) - i + 1 ≠ 0 := by
        have : (i : ℝ) < n := by exact_mod_cast (show i < n by omega)
        linarith
      have hu : u = (2 / i + ((n : ℝ) - i - 1) * v) / ((n : ℝ) - i + 1) := by
        rw [eq_div_iff hne]; linear_combination hr
      rw [hu]
      field_simp
      ring
    · have hn : (n : ℝ) = i + i := by exact_mod_cast h.symm
      simp only [fuHalfCov, coefA, coefB, coefC, coefD, fuSigma, lt_irrefl, h,
        show 2 * i = n by omega,
        ↓reduceIte]
      rw [fuBeta, tajimaA1_succ_eq_harm, tajimaA1_eq_harm hi, tajimaA1_eq_harm (by omega : 1 ≤ n)]
      have e1 : (n : ℝ) - i = i := by linarith
      rw [e1]
      field_simp
      ring
    · simp only [fuHalfCov, coefA, coefB, coefC, coefD, fuSigma, lt_irrefl,
        show ¬ (i + i < n) by omega, show i + i ≠ n by omega, show ¬ (2 * i < n) by omega,
        show 2 * i ≠ n by omega, ↓reduceIte]
      ring
  · have hmax : max i j = j := max_eq_right hlt.le
    have hmin : min i j = i := min_eq_left hlt.le
    rcases lt_trichotomy (i + j) n with h | h | h
    · have hri := fuBeta_rec hi (show i + 1 < n by omega)
      have hrj := fuBeta_rec (show 1 ≤ j by omega) (show j + 1 < n by omega)
      simp only [fuHalfCov, coefA, coefB, coefC, coefD, fuSigma, hlt, hmax,
        show ¬ (j < i) by omega, show i ≠ j by omega, show j ≠ i by omega, h,
        show j + i < n by omega, show i + j ≠ n by omega, show j + i ≠ n by omega,
        show i + 1 < n by omega, show j + 1 < n by omega, ↓reduceIte, cast_sub_sub_sub h,
        cast_sub_sub_sub (show j + i < n by omega)]
      set ui := fuBeta n i
      set vi := fuBeta n (i + 1)
      set uj := fuBeta n j
      set vj := fuBeta n (j + 1)
      have hnei : (n : ℝ) - i + 1 ≠ 0 := by
        have : (i : ℝ) < n := by exact_mod_cast (show i < n by omega)
        linarith
      have hnej : (n : ℝ) - j + 1 ≠ 0 := by
        have : (j : ℝ) < n := by exact_mod_cast hjn
        linarith
      have hij0 : (i : ℝ) + j ≠ 0 := by positivity
      have hui : ui = (2 / i + ((n : ℝ) - i - 1) * vi) / ((n : ℝ) - i + 1) := by
        rw [eq_div_iff hnei]; linear_combination hri
      have huj : uj = (2 / j + ((n : ℝ) - j - 1) * vj) / ((n : ℝ) - j + 1) := by
        rw [eq_div_iff hnej]; linear_combination hrj
      rw [hui, huj]
      field_simp
      ring
    · have hn : (n : ℝ) = i + j := by exact_mod_cast h.symm
      simp only [fuHalfCov, coefA, coefB, coefC, coefD, fuSigma, hlt, hmax, hmin,
        show ¬ (j < i) by omega, show i ≠ j by omega, show j ≠ i by omega, h, lt_irrefl,
        show j + i = n by omega, show i + 1 < n by omega, ↓reduceIte]
      rw [fuBeta.eq_1 n i, fuBeta.eq_1 n j, tajimaA1_succ_eq_harm, tajimaA1_eq_harm hi,
        tajimaA1_eq_harm (show 1 ≤ j by omega), tajimaA1_eq_harm (by omega : 1 ≤ n)]
      have e1 : (n : ℝ) - i = j := by linarith
      have e2 : (n : ℝ) - j = i := by linarith
      rw [e1, e2]
      field_simp
      ring
    · simp only [fuHalfCov, coefA, coefB, coefC, coefD, fuSigma, hlt, hmin,
        show ¬ (j < i) by omega, show i ≠ j by omega, show j ≠ i by omega,
        show ¬ (i + j < n) by omega, show ¬ (j + i < n) by omega, show i + j ≠ n by omega,
        show j + i ≠ n by omega, show i + 1 < n by omega, ↓reduceIte]
      ring

/-- **Fu's topology identity for every sample size**: `fuTopologyCov n i j = 4 σ_{ij}` for
`1 ≤ i, j ≤ n - 1`. -/
theorem fuTopologyCov_eq_four_mul_fuSigma (n : ℕ) :
    ∀ i ∈ Ico 1 n, ∀ j ∈ Ico 1 n, fuTopologyCov n i j = 4 * fuSigma n i j := by
  intro i hi j hj
  obtain ⟨hi1, hin⟩ := mem_Ico.1 hi
  obtain ⟨hj1, hjn⟩ := mem_Ico.1 hj
  rw [fuTopologyCov_eq_levelMoment hi1 hin hj1 hjn, sum_levelMoment hi1 hin hj1 hjn,
    sum_levelMoment hj1 hjn hi1 hin]
  rcases le_total i j with h | h
  · exact fuHalfCov_add_fuHalfCov hi1 h hjn
  · rw [fuSigma_comm, ← fuHalfCov_add_fuHalfCov hj1 h hin]
    ring

/-! ### Kingman's coalescent: `hσ` and Fu's SFS covariance without hypotheses -/

section Kingman

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
  {K : KingmanTimes μ n} {τ : Ω → List (List ℕ)}

/-- **`hσ` (Fu 1995)**: under Kingman's coalescent (holding times `K.T`) with an independent
block-size history `τ` with the random-joining law, `Cov(L_i, L_j) = 4 σ_{ij}` for
`1 ≤ i, j ≤ n - 1`. This is the hypothesis `hσ` of the theorems of `SFSFuClosedForm`. -/
theorem covariance_sfsLength_eq_four_mul_fuSigma
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ) :
    ∀ i ∈ Ico 1 n, ∀ j ∈ Ico 1 n,
      cov[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω),
        fun ω => sfsLength n j (τ ω) (fun k => K.T k ω); μ] = 4 * fuSigma n i j :=
  covariance_sfsLength_eq_four_mul_fuSigma_of_fuTopologyCov hτ hτ_law h_indep
    (fuTopologyCov_eq_four_mul_fuSigma n)

/-- **Variance of a linear combination of branch lengths** (Fu 1995):
`Var(∑_i c_i L_i) = 4 ∑_{i,j} c_i c_j σ_{ij}`. -/
theorem variance_sum_sfsLength_eq_fuSigma
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ) (c : ℕ → ℝ) :
    Var[fun ω => ∑ i ∈ Ico 1 n, c i * sfsLength n i (τ ω) (fun k => K.T k ω); μ] =
      4 * ∑ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, c i * c j * fuSigma n i j :=
  variance_sum_sfsLength_of_fuSigma hτ hτ_law
    (covariance_sfsLength_eq_four_mul_fuSigma hτ hτ_law h_indep) c

variable {θ : ℝ} {ξ : ℕ → Ω → ℝ}

/-- **Fu's covariance of the site frequency spectrum** (Fu 1995), for every sample size:
under Kingman's coalescent with an independent random-joining topology and the infinite-sites
mutation model, `Cov(ξ_i, ξ_j) = δ_{ij} θ / i + σ_{ij} θ²` for `1 ≤ i, j ≤ n - 1`. -/
theorem covariance_count_kingman_eq_fuSigma (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω)))
    {i j : ℕ} (hi : i ∈ Ico 1 n) (hj : j ∈ Ico 1 n) :
    cov[ξ i, ξ j; μ] = (if i = j then θ / i else 0) + θ ^ 2 * fuSigma n i j :=
  covariance_count_kingman_of_fuSigma hT hτ hτ_law h_indep h
    (covariance_sfsLength_eq_four_mul_fuSigma hτ hτ_law h_indep) hi hj

/-- **Variance of a linear SFS statistic** (Fu 1995), for every sample size:
`Var(∑_i a_i ξ_i) = θ ∑_i a_i² / i + θ² ∑_{i,j} a_i a_j σ_{ij}`. -/
theorem variance_sum_kingman_eq_fuSigma (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω)))
    (a : ℕ → ℝ) :
    Var[fun ω => ∑ i ∈ Ico 1 n, a i * ξ i ω; μ] =
      θ * ∑ i ∈ Ico 1 n, a i ^ 2 / i +
        θ ^ 2 * ∑ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, a i * a j * fuSigma n i j :=
  variance_sum_kingman_of_fuSigma hT hτ hτ_law h_indep h
    (covariance_sfsLength_eq_four_mul_fuSigma hτ hτ_law h_indep) a

end Kingman

end MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFuCovariance
