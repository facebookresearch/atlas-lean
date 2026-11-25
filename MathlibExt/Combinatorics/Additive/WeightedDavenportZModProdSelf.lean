/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/Combinatorics/Additive/ErdosGinzburgZiv.lean` (Mathlib):
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Yaël Dillies
-/

module

public import MathlibExt.Combinatorics.Additive.WeightedDavenportProd
import MathlibExt.Combinatorics.Additive.CombinatorialNullstellensatz
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Data.ZMod.Basic

/-!
# Weighted Davenport constant of $\mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/n\mathbb{Z}$

The main result, `weightedDavenport_zmod_prod_self_of_dvd`, shows that for natural numbers
$m, n \ge 2$ with $m \mid n$, every weight set $A$ with
$n/m \in A \subseteq \{1, \dots, \lceil n/(m-1) \rceil - 1\}$ has weighted Davenport constant
$D_A(\mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/n\mathbb{Z}) = 2m - 1$.

The lower bound is the coordinate-block construction `exists_weightedZeroSumFree_zmod_prod`.
For the upper bound, multiplying by the weight $n/m$ reduces the problem to Olson's bound
$D(\mathbb{Z}/m\mathbb{Z} \times \mathbb{Z}/m\mathbb{Z}) \le 2m - 1$. It is proved here for
integer vectors by induction on the prime factors of $m$, starting from the Chevalley–Warning
theorem for primes. These two steps adapt Mathlib's proof of the Erdős–Ginzburg–Ziv theorem
(`ZMod.erdos_ginzburg_ziv`).
-/

namespace MetaMathlibExt
namespace weightedDavenport_zmod_prod_self_of_dvd

open Finset MvPolynomial

-- Chevalley–Warning for the polynomials `∑ i ∈ S, f j i • X i ^ (p - 1)`, one for each `j`: a
-- nonzero common zero `y` selects the positions `i` with `y i ≠ 0`, where `y i ^ (p - 1) = 1`.
private theorem exists_sum_eq_zero {p : ℕ} [Fact p.Prime] {ι κ : Type*} [Fintype κ]
    (S : Finset ι) (f : κ → ι → ZMod p) (hS : Fintype.card κ * (p - 1) < #S) :
    ∃ T ⊆ S, T.Nonempty ∧ ∀ j, ∑ i ∈ T, f j i = 0 := by
  classical
  let F (j : κ) : MvPolynomial S (ZMod p) := ∑ i : S, f j i • X i ^ (p - 1)
  have hdeg : ∑ j ∈ univ, (F j).totalDegree < Fintype.card S := calc
    ∑ j ∈ univ, (F j).totalDegree ≤ ∑ _j : κ, (p - 1) := by
      gcongr with j
      exact totalDegree_finsetSum_le fun i _ =>
        (totalDegree_smul_le ..).trans (totalDegree_X_pow ..).le
    _ < Fintype.card S := by simpa using hS
  have hp : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
  obtain ⟨y, hy0, hy⟩ :=
    MathlibExt.Combinatorics.Additive.CombinatorialNullstellensatz.exists_ne_common_zero hdeg
      (x := 0) (by simp [F, hp])
  refine ⟨(univ.filter fun i : S => y i ≠ 0).map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨i, -, rfl⟩ := mem_map.mp hi
    exact i.2
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hy0
    exact ⟨i, mem_map.mpr ⟨i, by simpa using hi, rfl⟩⟩
  · intro j
    simpa [F, ZMod.pow_card_sub_one, sum_filter] using hy j (mem_univ j)

-- Integer vectors whose two coordinate sums vanish modulo `p` add up to a multiple of `p`.
private theorem exists_sum_eq_smul_of_cast {p : ℕ} {ι : Type*} (T : Finset ι) (v : ι → ℤ × ℤ)
    (h₁ : ∑ i ∈ T, ((v i).1 : ZMod p) = 0) (h₂ : ∑ i ∈ T, ((v i).2 : ZMod p) = 0) :
    ∃ w : ℤ × ℤ, ∑ i ∈ T, v i = (p : ℤ) • w := by
  rw [← Int.cast_sum, ZMod.intCast_zmod_eq_zero_iff_dvd] at h₁ h₂
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  exact ⟨(a, b), Prod.ext (by simpa [Prod.fst_sum] using ha) (by simpa [Prod.snd_sum] using hb)⟩

-- The Davenport bound for `(ℤ/pℤ)²`: among `2p - 1` integer vectors, some non-empty set of
-- them has sum in `p • ℤ²`.
private theorem exists_of_two_mul_sub_one_le {p : ℕ} [Fact p.Prime] {ι : Type*}
    (S : Finset ι) (v : ι → ℤ × ℤ) (hS : 2 * p - 1 ≤ #S) :
    ∃ T ⊆ S, T.Nonempty ∧ ∃ w : ℤ × ℤ, ∑ i ∈ T, v i = (p : ℤ) • w := by
  have hp := (Fact.out : p.Prime).two_le
  obtain ⟨T, hTS, hT, h⟩ := exists_sum_eq_zero (p := p) S
    (fun (b : Bool) i => if b then ((v i).1 : ZMod p) else ((v i).2 : ZMod p))
    (by simp only [Fintype.card_bool]; omega)
  exact ⟨T, hTS, hT, exists_sum_eq_smul_of_cast T v (by simpa using h true)
    (by simpa using h false)⟩

-- Among `3p - 2` integer vectors, some non-empty set of at most `p` of them has sum in
-- `p • ℤ²`. Chevalley–Warning with the extra polynomial `∑ X i ^ (p - 1)` gives such a set `T`
-- with `#T = p` or `#T = 2p`. In the second case, the Davenport bound gives such a set `U` among
-- all but one of the terms of `T`; then `U` or `T \ U` has at most `p` terms.
private theorem exists_card_le_of_three_mul_sub_two_le {p : ℕ} [Fact p.Prime] {ι : Type*}
    (S : Finset ι) (v : ι → ℤ × ℤ) (hS : 3 * p - 2 ≤ #S) :
    ∃ T ⊆ S, T.Nonempty ∧ #T ≤ p ∧ ∃ w : ℤ × ℤ, ∑ i ∈ T, v i = (p : ℤ) • w := by
  classical
  have hp := (Fact.out : p.Prime).two_le
  obtain ⟨S', hS'S, hS'⟩ := exists_subset_card_eq hS
  obtain ⟨T, hTS', hT, h⟩ := exists_sum_eq_zero (p := p) S'
    (fun (b : Option Bool) i => b.elim 1 fun c =>
      if c then ((v i).1 : ZMod p) else ((v i).2 : ZMod p))
    (by simp only [Fintype.card_option, Fintype.card_bool, hS']; omega)
  obtain ⟨w, hw⟩ := exists_sum_eq_smul_of_cast T v (by simpa using h (some true))
    (by simpa using h (some false))
  have hTS : T ⊆ S := hTS'.trans hS'S
  have hcard : #T ≤ 3 * p - 2 := hS' ▸ card_le_card hTS'
  obtain ⟨c, hc⟩ : p ∣ #T := by
    have h₀ := h none
    simp only [Option.elim_none, sum_const, nsmul_eq_mul, mul_one] at h₀
    exact (ZMod.natCast_eq_zero_iff _ _).mp h₀
  have hc3 : c < 3 := by
    by_contra! h3
    have := Nat.mul_le_mul_left p h3
    omega
  obtain rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  · simp [card_eq_zero.mp (by simpa using hc)] at hT
  · exact ⟨T, hTS, hT, by omega, w, hw⟩
  · obtain ⟨i₀, hi₀⟩ := hT
    obtain ⟨U, hUT, hU, u, hu⟩ := exists_of_two_mul_sub_one_le (p := p) (T.erase i₀) v
      (by rw [card_erase_of_mem hi₀]; omega)
    have hUT' : U ⊆ T := hUT.trans (erase_subset i₀ T)
    by_cases hUp : #U ≤ p
    · exact ⟨U, hUT'.trans hTS, hU, hUp, u, hu⟩
    · refine ⟨T \ U, sdiff_subset.trans hTS, ⟨i₀, mem_sdiff.mpr ⟨hi₀, fun hi => ?_⟩⟩, ?_,
        w - u, ?_⟩
      · simpa using hUT hi
      · rw [card_sdiff_of_subset hUT']
        omega
      · rw [smul_sub, ← hw, ← hu, eq_sub_iff_add_eq, sum_sdiff hUT']

-- Removing zero sums one at a time: from `j p + 2p - 1` integer vectors one can take `j + 1`
-- pairwise disjoint non-empty sets of them, each with sum in `p • ℤ²`.
private theorem exists_disjoint_family {p : ℕ} [Fact p.Prime] {ι : Type*} (v : ι → ℤ × ℤ)
    (j : ℕ) (S : Finset ι) (hS : j * p + (2 * p - 1) ≤ #S) :
    ∃ 𝒜 : Finset (Finset ι), #𝒜 = j + 1 ∧ (𝒜 : Set (Finset ι)).PairwiseDisjoint id ∧
      ∀ T ∈ 𝒜, T ⊆ S ∧ T.Nonempty ∧ ∃ w : ℤ × ℤ, ∑ i ∈ T, v i = (p : ℤ) • w := by
  classical
  induction j generalizing S with
  | zero =>
    obtain ⟨T, hTS, hT, hw⟩ := exists_of_two_mul_sub_one_le S v (by simpa using hS)
    refine ⟨{T}, card_singleton T, by simp, fun U hU => ?_⟩
    rw [mem_singleton.mp hU]
    exact ⟨hTS, hT, hw⟩
  | succ j ih =>
    have hp := (Fact.out : p.Prime).two_le
    rw [Nat.succ_mul] at hS
    obtain ⟨T, hTS, hT, hTp, hw⟩ :=
      exists_card_le_of_three_mul_sub_two_le (p := p) S v (by omega)
    obtain ⟨𝒜, h𝒜card, h𝒜disj, h𝒜⟩ := ih (S \ T) (by rw [card_sdiff_of_subset hTS]; omega)
    have hT𝒜 : T ∉ 𝒜 := fun hmem => by
      obtain ⟨i, hi⟩ := hT
      simpa [hi] using (h𝒜 T hmem).1 hi
    refine ⟨insert T 𝒜, by rw [card_insert_of_notMem hT𝒜, h𝒜card], ?_, ?_⟩
    · rw [coe_insert]
      exact h𝒜disj.insert fun U hU _ => disjoint_sdiff.mono_right (h𝒜 U hU).1
    · intro U hU
      rcases mem_insert.mp hU with rfl | hU
      · exact ⟨hTS, hT, hw⟩
      · obtain ⟨hUS, hU', hw'⟩ := h𝒜 U hU
        exact ⟨hUS.trans sdiff_subset, hU', hw'⟩

-- Olson's bound `D((ℤ/mℤ)²) ≤ 2m - 1` for integer vectors. For `m = p m'` with `p` prime, take
-- `2m' - 1` disjoint sets with sums `p • w T`, then apply the bound for `m'` to the `w T`.
private theorem exists_sum_eq_smul (m : ℕ) : 0 < m → ∀ {ι : Type*} (S : Finset ι)
    (v : ι → ℤ × ℤ), 2 * m - 1 ≤ #S →
      ∃ T ⊆ S, T.Nonempty ∧ ∃ w : ℤ × ℤ, ∑ i ∈ T, v i = (m : ℤ) • w := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm ι S v hS
  classical
  obtain rfl | hm1 := eq_or_ne m 1
  · obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 < #S)
    exact ⟨{i}, singleton_subset_iff.mpr hi, singleton_nonempty i, v i, by simp⟩
  obtain ⟨p, hp, m', rfl⟩ := Nat.exists_prime_and_dvd hm1
  have : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  have hm' : 0 < m' := Nat.pos_of_ne_zero fun h => by simp [h] at hm
  have hlt : m' < p * m' := lt_mul_left hm' hp.one_lt
  have hsplit : (2 * m' - 2) * p + 2 * p = 2 * (p * m') := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega), Nat.mul_assoc, Nat.mul_comm m' p]
  obtain ⟨𝒜, h𝒜card, h𝒜disj, h𝒜⟩ :=
    exists_disjoint_family (p := p) v (2 * m' - 2) S (by omega)
  choose! w hw using fun T hT => (h𝒜 T hT).2.2
  obtain ⟨ℬ, hℬ𝒜, hℬ, u, hu⟩ := ih m' hlt hm' 𝒜 w (by omega)
  refine ⟨ℬ.biUnion id, biUnion_subset.mpr fun T hT => (h𝒜 T (hℬ𝒜 hT)).1, ?_, u, ?_⟩
  · obtain ⟨T, hT⟩ := hℬ
    obtain ⟨i, hi⟩ := (h𝒜 T (hℬ𝒜 hT)).2.1
    exact ⟨i, mem_biUnion.mpr ⟨T, hT, hi⟩⟩
  · rw [sum_biUnion (h𝒜disj.subset (coe_subset.mpr hℬ𝒜))]
    calc ∑ T ∈ ℬ, ∑ i ∈ id T, v i = ∑ T ∈ ℬ, (p : ℤ) • w T :=
          sum_congr rfl fun T hT => hw T (hℬ𝒜 hT)
      _ = ((p * m' : ℕ) : ℤ) • u := by rw [← smul_sum, hu, smul_smul, Nat.cast_mul]

end weightedDavenport_zmod_prod_self_of_dvd

open weightedDavenport_zmod_prod_self_of_dvd in
/-- **Weight sets with weighted Davenport constant $2m - 1$ on
$\mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/n\mathbb{Z}$.** Let $n \ge 2$ be a natural number and
$m \ge 2$ a divisor of $n$. Every finite set $A$ of natural numbers with
$n/m \in A \subseteq \{1, \dots, \lceil n/(m-1) \rceil - 1\}$ has $A$-weighted Davenport constant
$D_A(\mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/n\mathbb{Z}) = 2m - 1$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Corollary 2 (`integers-2026-A89-cor-2`). -/
public theorem weightedDavenport_zmod_prod_self_of_dvd (m n : ℕ) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (hdvd : m ∣ n) (A : Finset ℕ) (hmem : n / m ∈ A)
    (hsub : A ⊆ Finset.Icc 1 (n ⌈/⌉ (m - 1) - 1)) :
    weightedDavenport A (ZMod n × ZMod n) = ((2 * m - 1 : ℕ) : ℕ∞) := by
  apply le_antisymm
  · -- Lift to integer vectors, find a sum in `m • ℤ²` and scale it by the weight `n / m`.
    apply weightedDavenport_le
    intro s hs hfree
    have : NeZero n := ⟨by omega⟩
    let φ : ℤ × ℤ →+ ZMod n × ZMod n :=
      (Int.castAddHom (ZMod n)).prodMap (Int.castAddHom (ZMod n))
    let v (i : Fin s.length) : ℤ × ℤ := ((s.get i).1.val, (s.get i).2.val)
    have hv (i : Fin s.length) : φ (v i) = s.get i := by
      simp [φ, v]
    obtain ⟨T, -, hT, w, hw⟩ := exists_sum_eq_smul m (by omega) Finset.univ v (by simp [hs])
    apply hfree T hT (fun _ => n / m) (fun _ _ => hmem)
    calc ∑ i ∈ T, (n / m) • s.get i = φ ((n / m) • ∑ i ∈ T, v i) := by
          simp only [map_nsmul, map_sum, hv, Finset.smul_sum]
      _ = φ (n • w) := by rw [hw, natCast_zsmul, smul_smul, Nat.div_mul_cancel hdvd]
      _ = 0 := by
          rw [map_nsmul]
          ext <;> simp [nsmul_eq_mul]
  · -- The coordinate blocks of Lemma 2 for `k = 1` have length `2m - 2` by Lemma 1.
    have h := exists_weightedZeroSumFree_zmod_prod m n 1 hm hn hdvd le_rfl
    rw [Nat.one_mul, ceilDiv_ceilDiv_sub_one_sub_one_of_dvd m n hm hn hdvd] at h
    obtain ⟨s, hlen, hfree⟩ := h
    have hA : IsWeightedZeroSumFree A s :=
      fun I hI a ha => hfree I hI a fun i hi => hsub (ha i hi)
    rw [show 2 * m - 1 = s.length + 1 by omega, Nat.cast_add_one]
    exact Order.add_one_le_of_lt (lt_weightedDavenport hA)

end MetaMathlibExt
