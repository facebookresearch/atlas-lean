/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CompletelyAdditiveHeight
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Card
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Bounds.Basic

/-!
# Realizing a prescribed profile

For a profile with infinite support, the cumulative sums are unbounded, so every
positive index lies in a unique block between successive partial sums. Transporting
the block index along the prime enumeration gives, via the canonical sequential
realization, a height function with exactly `π k` primes at each height `k ≥ 1`.

Statements from Hartosh Singh Bal, *Completely Additive Height Functions: Profile
Laws, Matula Bounds, and Inverse Growth*, INTEGERS 26 (2026), Article A116.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem profilePartialSum_zero (π : ℕ → ℕ) : profilePartialSum π 0 = 0 := by
  simp [profilePartialSum]

private theorem profilePartialSum_mono (π : ℕ → ℕ) : Monotone (profilePartialSum π) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [profilePartialSum_succ]
  exact Nat.le_add_right _ _

private theorem profilePartialSum_unbounded (π : ℕ → ℕ)
    (hπ : {k : ℕ | 1 ≤ k ∧ π k ≠ 0}.Infinite) (B : ℕ) :
    ∃ k, B ≤ profilePartialSum π k := by
  obtain ⟨t, hts, hfin, hcard⟩ := hπ.exists_subset_ncard_eq (B + 1)
  obtain ⟨K, hK⟩ := hfin.bddAbove
  refine ⟨K, ?_⟩
  have hsub : hfin.toFinset ⊆ Finset.Icc 1 K := by
    intro x hx
    have hxt : x ∈ t := (hfin.mem_toFinset).mp hx
    have h1 : 1 ≤ x := (hts hxt).1
    have h2 : x ≤ K := hK hxt
    exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  have h1le : ∀ x ∈ hfin.toFinset, 1 ≤ π x := by
    intro x hx
    have hxt : x ∈ t := (hfin.mem_toFinset).mp hx
    have hne : π x ≠ 0 := (hts hxt).2
    exact Nat.one_le_iff_ne_zero.mpr hne
  have hsum1 : ∑ x ∈ hfin.toFinset, 1 ≤ ∑ x ∈ hfin.toFinset, π x :=
    Finset.sum_le_sum fun x hx => h1le x hx
  have hsum2 : ∑ x ∈ hfin.toFinset, π x ≤ ∑ x ∈ Finset.Icc 1 K, π x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => Nat.zero_le _)
  have hcard2 : hfin.toFinset.card = B + 1 := by
    rw [← Set.ncard_eq_toFinset_card t hfin, hcard]
  have hsum0 : ∑ x ∈ hfin.toFinset, 1 = hfin.toFinset.card := by simp
  have hle : B + 1 ≤ profilePartialSum π K := by
    unfold profilePartialSum
    omega
  omega

private theorem seqHeightIndex_nonempty (π : ℕ → ℕ)
    (hπ : {k : ℕ | 1 ≤ k ∧ π k ≠ 0}.Infinite) (i : ℕ) :
    {k | i ≤ profilePartialSum π k}.Nonempty := by
  obtain ⟨k, hk⟩ := profilePartialSum_unbounded π hπ i
  exact ⟨k, hk⟩

private theorem seqHeightIndex_mem (π : ℕ → ℕ)
    (hπ : {k : ℕ | 1 ≤ k ∧ π k ≠ 0}.Infinite) (i : ℕ) :
    i ≤ profilePartialSum π (seqHeightIndex π i) :=
  csInf_mem (seqHeightIndex_nonempty π hπ i)

private theorem seqHeightIndex_le (π : ℕ → ℕ) (i k : ℕ)
    (hk : i ≤ profilePartialSum π k) : seqHeightIndex π i ≤ k :=
  csInf_le (OrderBot.bddBelow _) hk

private theorem seqHeightIndex_min (π : ℕ → ℕ) (i k : ℕ)
    (hk : k < seqHeightIndex π i) : profilePartialSum π k < i := by
  by_contra h
  have h' : i ≤ profilePartialSum π k := Nat.le_of_not_gt h
  have hle := seqHeightIndex_le π i k h'
  omega

private theorem seqHeightIndex_ge_one (π : ℕ → ℕ)
    (hπ : {k : ℕ | 1 ≤ k ∧ π k ≠ 0}.Infinite) (i : ℕ) (hi : 1 ≤ i) :
    1 ≤ seqHeightIndex π i := by
  have hmem := seqHeightIndex_mem π hπ i
  have h0 : ¬ i ≤ profilePartialSum π 0 := by
    rw [profilePartialSum_zero]
    omega
  have hne : seqHeightIndex π i ≠ 0 := fun h => h0 (h ▸ hmem)
  omega

private theorem profilePartialSum_pred_add (π : ℕ → ℕ) (k : ℕ) (hk : 1 ≤ k) :
    profilePartialSum π k = profilePartialSum π (k - 1) + π k := by
  have h : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have h2 := profilePartialSum_succ π (k - 1)
  rw [h] at h2
  exact h2

private theorem seqHeightIndex_eq_iff (π : ℕ → ℕ)
    (hπ : {k : ℕ | 1 ≤ k ∧ π k ≠ 0}.Infinite) (i k : ℕ) (hk : 1 ≤ k) :
    seqHeightIndex π i = k ↔
      profilePartialSum π (k - 1) < i ∧ i ≤ profilePartialSum π k := by
  constructor
  · intro h
    refine ⟨?_, h ▸ seqHeightIndex_mem π hπ i⟩
    have hlt : k - 1 < seqHeightIndex π i := by omega
    exact seqHeightIndex_min π i (k - 1) hlt
  · rintro ⟨hlt, hle⟩
    have h1 : seqHeightIndex π i ≤ k := seqHeightIndex_le π i k hle
    have h2 : k ≤ seqHeightIndex π i := by
      by_contra h
      have hlt' : seqHeightIndex π i < k := Nat.lt_of_not_ge h
      have hle2 : seqHeightIndex π i ≤ k - 1 := by omega
      have hmono := profilePartialSum_mono π hle2
      have hmem := seqHeightIndex_mem π hπ i
      omega
    omega

private theorem index_level_eq (π : ℕ → ℕ)
    (hπ : {k : ℕ | 1 ≤ k ∧ π k ≠ 0}.Infinite) (k : ℕ) (hk : 1 ≤ k) :
    {i : ℕ | 1 ≤ i ∧ seqHeightIndex π i = k} =
      Set.Ioc (profilePartialSum π (k - 1)) (profilePartialSum π k) := by
  ext i
  simp only [Set.mem_Ioc]
  constructor
  · rintro ⟨_, hi⟩
    exact (seqHeightIndex_eq_iff π hπ i k hk).mp hi
  · rintro ⟨hlt, hle⟩
    have hi1 : 1 ≤ i := by
      have hnn : 0 ≤ profilePartialSum π (k - 1) := Nat.zero_le _
      omega
    exact ⟨hi1, (seqHeightIndex_eq_iff π hπ i k hk).mpr ⟨hlt, hle⟩⟩

private theorem index_level_ncard (π : ℕ → ℕ)
    (hπ : {k : ℕ | 1 ≤ k ∧ π k ≠ 0}.Infinite) (k : ℕ) (hk : 1 ≤ k) :
    {i : ℕ | 1 ≤ i ∧ seqHeightIndex π i = k}.ncard = π k := by
  rw [index_level_eq π hπ k hk, Set.ncard_Ioc, Nat.card_Ioc]
  have h := profilePartialSum_pred_add π k hk
  omega

private theorem nthPrimeOne_prime (i : ℕ) : (nthPrimeOne i).Prime := by
  unfold nthPrimeOne
  exact Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (i - 1)

private theorem count_nthPrimeOne (i : ℕ) (hi : 1 ≤ i) :
    Nat.count Nat.Prime (nthPrimeOne i) + 1 = i := by
  unfold nthPrimeOne
  rw [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime]
  omega

private theorem nthPrimeOne_count (p : ℕ) (hp : p.Prime) :
    nthPrimeOne (Nat.count Nat.Prime p + 1) = p := by
  unfold nthPrimeOne
  rw [Nat.add_sub_cancel]
  exact Nat.nth_count hp

private theorem canonicalSeqHeight_nthPrimeOne (π : ℕ → ℕ) (i : ℕ) (hi : 1 ≤ i) :
    canonicalSeqHeight π (nthPrimeOne i) = seqHeightIndex π i := by
  unfold canonicalSeqHeight
  rw [additiveOfPrimeValues_prime _ (nthPrimeOne_prime i), count_nthPrimeOne i hi]

private theorem prime_level_eq (π : ℕ → ℕ) (k : ℕ) :
    {p : ℕ | p.Prime ∧ canonicalSeqHeight π p = k} =
      nthPrimeOne '' {i : ℕ | 1 ≤ i ∧ seqHeightIndex π i = k} := by
  ext p
  constructor
  · rintro ⟨hp, hH⟩
    have hH' : canonicalSeqHeight π p = seqHeightIndex π (Nat.count Nat.Prime p + 1) := by
      unfold canonicalSeqHeight
      rw [additiveOfPrimeValues_prime _ hp]
    exact ⟨Nat.count Nat.Prime p + 1, ⟨by omega, hH'.symm.trans hH⟩,
      nthPrimeOne_count p hp⟩
  · rintro ⟨i, ⟨hi, hki⟩, rfl⟩
    exact ⟨nthPrimeOne_prime i, by rw [canonicalSeqHeight_nthPrimeOne π i hi, hki]⟩

private theorem nthPrimeOne_injOn (π : ℕ → ℕ) (k : ℕ) :
    Set.InjOn nthPrimeOne {i : ℕ | 1 ≤ i ∧ seqHeightIndex π i = k} := by
  intro i hi j hj hij
  obtain ⟨hi1, -⟩ := hi
  obtain ⟨hj1, -⟩ := hj
  unfold nthPrimeOne at hij
  have hinj := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective
  have h : i - 1 = j - 1 := hinj hij
  omega

private theorem prime_level_ncard (π : ℕ → ℕ)
    (hπ : {k : ℕ | 1 ≤ k ∧ π k ≠ 0}.Infinite) (k : ℕ) (hk : 1 ≤ k) :
    {p : ℕ | p.Prime ∧ canonicalSeqHeight π p = k}.ncard = π k := by
  rw [prime_level_eq π k, (nthPrimeOne_injOn π k).ncard_image]
  exact index_level_ncard π hπ k hk

private theorem prime_level_finite (π : ℕ → ℕ)
    (hπ : {k : ℕ | 1 ≤ k ∧ π k ≠ 0}.Infinite) (n : ℕ) (hn : 1 ≤ n) :
    {p : ℕ | p.Prime ∧ canonicalSeqHeight π p = n}.Finite := by
  rw [prime_level_eq π n]
  have hfin : {i : ℕ | 1 ≤ i ∧ seqHeightIndex π i = n}.Finite := by
    rw [index_level_eq π hπ n hn, ← Finset.coe_Ioc]
    exact Finset.finite_toSet _
  exact hfin.image _

/-- **Realizing a prescribed profile.** Let $(\pi_k)_{k \ge 1}$ be nonnegative integers with
$\pi_k \ne 0$ for infinitely many $k$ (equivalently, $\sum_k \pi_k = \infty$). Then there is a
height function $H$ such that for every $k \ge 1$ exactly $\pi_k$ primes $p$ satisfy $H(p) = k$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 2
(`integers-2026-A116-prop-2`). -/
public theorem exists_heightFunction_with_profile (π : ℕ → ℕ)
    (hπ : {k : ℕ | 1 ≤ k ∧ π k ≠ 0}.Infinite) :
    ∃ H : ℕ → ℕ, IsHeightFunction H ∧ ∀ k, 1 ≤ k → {p : ℕ | p.Prime ∧ H p = k}.ncard = π k := by
  refine ⟨canonicalSeqHeight π, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact isCompletelyAdditiveNat_additiveOfPrimeValues _
  · intro p hp
    unfold canonicalSeqHeight
    rw [additiveOfPrimeValues_prime _ hp]
    exact seqHeightIndex_ge_one π hπ _ (by omega)
  · intro n hn
    exact prime_level_finite π hπ n hn
  · intro k hk
    exact prime_level_ncard π hπ k hk

end

end MetaMathlibExt
