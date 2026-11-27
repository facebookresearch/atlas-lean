/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Rayleigh
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Computability.Reduce
import Mathlib.Data.Int.Star

namespace MetaMathlibExt

@[expose] public section

open Classical in
private theorem count_beatty (k : ℕ) (α : Fin k → ℝ)
    (hαpos : ∀ i, 0 < α i) (hαlt : ∀ i, α i < 1)
    (hdisj : (Set.univ : Set (Fin k)).PairwiseDisjoint
      (fun i => {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}))
    (hcover : (⋃ i, {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}) =
      {x : ℤ | 0 < x})
    (N : ℕ) :
    ∑ i : Fin k, ⌈((N : ℝ) + 1) * α i⌉ = (N : ℤ) + (k : ℤ) := by
  have hβpos : ∀ i, 0 < (1 : ℝ) / α i := fun i => one_div_pos.mpr (hαpos i)
  have hβgt : ∀ i, 1 < (1 : ℝ) / α i := by
    intro i
    rw [lt_div_iff₀ (hαpos i)]
    linarith [hαlt i]
  have hαne : ∀ i, α i ≠ 0 := fun i => ne_of_gt (hαpos i)
  have hαβ : ∀ i, α i * (1 / α i) = 1 :=
    fun i => mul_one_div_cancel (hαne i)
  have hβα : ∀ i, (1 : ℝ) / α i * α i = 1 :=
    fun i => one_div_mul_cancel (hαne i)
  have hmono : ∀ i, StrictMono (fun n : ℤ => ⌊(n : ℝ) * (1 / α i)⌋) := by
    intro i a b hab
    simp only
    have ha1 : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast (by omega : a + 1 ≤ b)
    have h2 : ((a : ℝ) + 1) * (1 / α i) ≤ (b : ℝ) * (1 / α i) :=
      mul_le_mul_of_nonneg_right ha1 (le_of_lt (hβpos i))
    have h3 : (a : ℝ) * (1 / α i) + 1 < (b : ℝ) * (1 / α i) := by
      have hexpand : ((a : ℝ) + 1) * (1 / α i) = (a : ℝ) * (1 / α i) + 1 / α i := by
        ring
      linarith [hβgt i]
    have hle : ⌊(a : ℝ) * (1 / α i)⌋ + 1 ≤ ⌊(b : ℝ) * (1 / α i)⌋ := by
      have hfl := Int.floor_le_floor (le_of_lt h3)
      rwa [Int.floor_add_one] at hfl
    omega
  have hP1 : ∀ (i : Fin k) (n : ℤ), ⌊(n : ℝ) * (1 / α i)⌋ ≤ (N : ℤ) →
      n ≤ ⌈((N : ℝ) + 1) * α i⌉ - 1 := by
    intro i n hn
    have hlt : (n : ℝ) * (1 / α i) < (N : ℝ) + 1 := by
      have h := Int.floor_le_iff.mp hn
      push_cast at h ⊢
      linarith
    have hnX : (n : ℝ) < ((N : ℝ) + 1) * α i := by
      have hmul := mul_lt_mul_of_pos_right hlt (hαpos i)
      have heq : (n : ℝ) = ((n : ℝ) * (1 / α i)) * α i := by
        rw [mul_assoc, hβα i, mul_one]
      linarith
    have hle : (n : ℝ) < (⌈((N : ℝ) + 1) * α i⌉ : ℝ) :=
      lt_of_lt_of_le hnX (Int.le_ceil _)
    have hlt2 : n < ⌈((N : ℝ) + 1) * α i⌉ := by exact_mod_cast hle
    omega
  have hP2 : ∀ (i : Fin k) (n : ℤ), n ≤ ⌈((N : ℝ) + 1) * α i⌉ - 1 →
      ⌊(n : ℝ) * (1 / α i)⌋ ≤ (N : ℤ) := by
    intro i n hn
    have hnX : (n : ℝ) < ((N : ℝ) + 1) * α i := by
      have h1 : (n : ℝ) ≤ ((⌈((N : ℝ) + 1) * α i⌉ - 1 : ℤ) : ℝ) := by exact_mod_cast hn
      have h2 : ((⌈((N : ℝ) + 1) * α i⌉ - 1 : ℤ) : ℝ) < ((N : ℝ) + 1) * α i := by
        have hcl := Int.ceil_lt_add_one (((N : ℝ) + 1) * α i)
        push_cast at hcl ⊢
        linarith
      linarith
    have hmul := mul_lt_mul_of_pos_right hnX (hβpos i)
    have heq : (((N : ℝ) + 1) * α i) * (1 / α i) = (N : ℝ) + 1 := by
      rw [mul_assoc, hαβ i, mul_one]
    rw [heq] at hmul
    have hmul2 : (n : ℝ) * (1 / α i) < (((N : ℤ)) : ℝ) + 1 := by
      rw [Int.cast_natCast]
      exact hmul
    exact Int.floor_le_iff.mpr hmul2
  have hP3 : ∀ (i : Fin k) (n : ℤ), 1 ≤ n → 1 ≤ ⌊(n : ℝ) * (1 / α i)⌋ := by
    intro i n hn
    have hnβ : (1 : ℝ) * (1 / α i) ≤ (n : ℝ) * (1 / α i) := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt (hβpos i))
      exact_mod_cast hn
    have h1 : (1 : ℤ) ≤ ⌊(1 : ℝ) * (1 / α i)⌋ := by
      rw [Int.le_floor]
      simp only [Int.cast_one, one_mul]
      exact le_of_lt (hβgt i)
    calc (1 : ℤ) ≤ ⌊(1 : ℝ) * (1 / α i)⌋ := h1
      _ ≤ ⌊(n : ℝ) * (1 / α i)⌋ := Int.floor_le_floor hnβ
  have hfilter : ∀ i : Fin k, (Finset.Icc (1 : ℤ) (N : ℤ)).filter
      (fun x => x ∈ {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}) =
      (Finset.Icc (1 : ℤ) (⌈((N : ℝ) + 1) * α i⌉ - 1)).image
        (fun (n : ℤ) => ⌊(n : ℝ) * (1 / α i)⌋) := by
    intro i
    ext x
    rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    simp only [Set.mem_ofPred_eq, beattySeq]
    constructor
    · rintro ⟨⟨h1x, hxN⟩, n, hn0, hnx⟩
      refine ⟨n, Finset.mem_Icc.mpr ⟨?_, hP1 i n (hnx ▸ hxN)⟩, hnx⟩
      omega
    · rintro ⟨n, hn, hnx⟩
      have hnIcc := Finset.mem_Icc.mp hn
      have hxN : x ≤ (N : ℤ) := hnx ▸ hP2 i n hnIcc.2
      have h1x : (1 : ℤ) ≤ x := hnx ▸ hP3 i n hnIcc.1
      exact ⟨⟨h1x, hxN⟩, n, by omega, hnx⟩
  have hTdisj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun i => (Finset.Icc (1 : ℤ) (N : ℤ)).filter
        (fun x => x ∈ {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x})) := by
    intro i _ j _ hij
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hiS : x ∈ {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x} :=
      (Finset.mem_filter.mp hxi).2
    have hjS : x ∈ {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α j) n = x} :=
      (Finset.mem_filter.mp hxj).2
    exact Set.disjoint_left.mp (hdisj (Set.mem_univ i) (Set.mem_univ j) hij) hiS hjS
  have hTcover : Finset.univ.biUnion
      (fun i => (Finset.Icc (1 : ℤ) (N : ℤ)).filter
        (fun x => x ∈ {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x})) =
      Finset.Icc (1 : ℤ) (N : ℤ) := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨i, _, hxi⟩ := hx
      exact (Finset.mem_filter.mp hxi).1
    · intro hx
      rw [Finset.mem_biUnion]
      have hxIcc : 1 ≤ x ∧ x ≤ (N : ℤ) := Finset.mem_Icc.mp hx
      have hxpos : x ∈ {x : ℤ | 0 < x} := by
        show (0 : ℤ) < x
        omega
      rw [← hcover] at hxpos
      obtain ⟨j, hxS⟩ := Set.mem_iUnion.mp hxpos
      exact ⟨j, Finset.mem_univ j, Finset.mem_filter.mpr ⟨hx, hxS⟩⟩
  have hcardIcc : (Finset.Icc (1 : ℤ) (N : ℤ)).card = N := by
    rw [Int.card_Icc]
    have hrw : (N : ℤ) + 1 - 1 = (N : ℤ) := by ring
    rw [hrw, Int.toNat_natCast]
  have hTcard : ∀ i : Fin k, ((Finset.Icc (1 : ℤ) (N : ℤ)).filter
      (fun x => x ∈ {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x})).card =
      (⌈((N : ℝ) + 1) * α i⌉ - 1).toNat := by
    intro i
    rw [hfilter i, Finset.card_image_of_injective _ (hmono i).injective, Int.card_Icc]
    have hrw : ⌈((N : ℝ) + 1) * α i⌉ - 1 + 1 - 1 = ⌈((N : ℝ) + 1) * α i⌉ - 1 := by ring
    rw [hrw]
  have hcnonneg : ∀ i : Fin k, 0 ≤ ⌈((N : ℝ) + 1) * α i⌉ - 1 := by
    intro i
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hpos : (0 : ℝ) < ((N : ℝ) + 1) * α i := mul_pos hN1 (hαpos i)
    have h1 := Int.ceil_pos.mpr hpos
    omega
  have hsum : (Finset.Icc (1 : ℤ) (N : ℤ)).card = ∑ i : Fin k,
      (((Finset.Icc (1 : ℤ) (N : ℤ)).filter
        (fun x => x ∈ {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x})).card) := by
    have hbi := Finset.card_biUnion hTdisj
    rw [hTcover] at hbi
    simpa using hbi
  rw [hcardIcc] at hsum
  have hZ : (N : ℤ) = ∑ i : Fin k, (⌈((N : ℝ) + 1) * α i⌉ - 1) := by
    have hsumZ := congrArg (Nat.cast : ℕ → ℤ) hsum.symm
    rw [Nat.cast_sum] at hsumZ
    rw [← hsumZ]
    apply Finset.sum_congr rfl
    intro i _
    rw [hTcard i]
    exact Int.toNat_of_nonneg (hcnonneg i)
  have hsub : (∑ i : Fin k, (⌈((N : ℝ) + 1) * α i⌉ - 1)) =
      (∑ i : Fin k, ⌈((N : ℝ) + 1) * α i⌉) - (k : ℤ) := by
    rw [Finset.sum_sub_distrib]
    have hone : (∑ _x : Fin k, (1 : ℤ)) = (k : ℤ) := by simp
    rw [hone]
  rw [hsub] at hZ
  omega

-- Ceil-sum identity for multiplier M ≥ 1 (from counting with N = M - 1).
private theorem ceil_sum (k : ℕ) (α : Fin k → ℝ)
    (hαpos : ∀ i, 0 < α i) (hαlt : ∀ i, α i < 1)
    (hdisj : (Set.univ : Set (Fin k)).PairwiseDisjoint
      (fun i => {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}))
    (hcover : (⋃ i, {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}) =
      {x : ℤ | 0 < x})
    (M : ℕ) (hM : 1 ≤ M) :
    ∑ i : Fin k, ⌈(M : ℝ) * α i⌉ = (M : ℤ) + (k : ℤ) - 1 := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hN := count_beatty k α hαpos hαlt hdisj hcover M'
  have eR : ((M' : ℕ) : ℝ) + 1 = ((M' + 1 : ℕ) : ℝ) := by push_cast; ring
  have eZ : ((M' : ℕ) : ℤ) = ((M' + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
  rw [eR, eZ] at hN
  omega

-- The densities sum to 1 (squeeze with Archimedean).
private theorem sum_alpha (k : ℕ) (α : Fin k → ℝ)
    (hαpos : ∀ i, 0 < α i) (hαlt : ∀ i, α i < 1)
    (hdisj : (Set.univ : Set (Fin k)).PairwiseDisjoint
      (fun i => {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}))
    (hcover : (⋃ i, {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}) =
      {x : ℤ | 0 < x})
    (hk1 : 1 ≤ k) :
    ∑ i : Fin k, α i = 1 := by
  set S := ∑ i : Fin k, α i with hSdef
  have hbnds : ∀ M : ℕ, 1 ≤ M →
      (M : ℝ) * S ≤ ((∑ i : Fin k, ⌈(M : ℝ) * α i⌉ : ℤ) : ℝ) ∧
      ((∑ i : Fin k, ⌈(M : ℝ) * α i⌉ : ℤ) : ℝ) < (M : ℝ) * S + (k : ℝ) := by
    intro M _
    have hcast : ((∑ i : Fin k, ⌈(M : ℝ) * α i⌉ : ℤ) : ℝ) =
        ∑ i : Fin k, ((⌈(M : ℝ) * α i⌉ : ℤ) : ℝ) := Int.cast_sum _ _
    have hmul : (M : ℝ) * S = ∑ i : Fin k, (M : ℝ) * α i := by
      rw [hSdef, Finset.mul_sum]
    rw [hcast, hmul]
    constructor
    · exact Finset.sum_le_sum (fun i _ => Int.le_ceil _)
    · have hlt : ∑ i : Fin k, ((⌈(M : ℝ) * α i⌉ : ℤ) : ℝ) <
          ∑ i : Fin k, ((M : ℝ) * α i + 1) := by
        apply Finset.sum_lt_sum
        · intro i _
          have h := Int.ceil_lt_add_one ((M : ℝ) * α i)
          linarith
        · have hne : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
          obtain ⟨i₀⟩ := hne
          exact ⟨i₀, Finset.mem_univ i₀, by
            have h := Int.ceil_lt_add_one ((M : ℝ) * α i₀)
            linarith⟩
      have heq : (∑ i : Fin k, ((M : ℝ) * α i + 1)) = (∑ i : Fin k, (M : ℝ) * α i) + (k : ℝ) := by
        rw [Finset.sum_add_distrib]
        congr 1
        simp
      linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- S < 1: use upper bound with large M.
    have hδ : (0 : ℝ) < 1 - S := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - S))
    have hn0 : 0 < n := by
      have hnn : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (by positivity) hn
      exact Nat.cast_pos.mp hnn
    have hn1 : 1 ≤ n := hn0
    have hnS : (1 : ℝ) < (n : ℝ) * (1 - S) := by
      have h := (div_lt_iff₀ hδ).mp hn
      linarith
    have hceil := ceil_sum k α hαpos hαlt hdisj hcover n hn1
    have hcast : ((∑ i : Fin k, ⌈(n : ℝ) * α i⌉ : ℤ) : ℝ) = (n : ℝ) + (k : ℝ) - 1 := by
      exact_mod_cast hceil
    have hub := (hbnds n hn1).2
    rw [hcast] at hub
    nlinarith
  · -- S > 1: use lower bound with large M.
    have hδ : (0 : ℝ) < S - 1 := by linarith
    have hk0 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (((k : ℝ) - 1) / (S - 1))
    have hn0 : 0 < n := by
      have hnn : (0 : ℝ) < (n : ℝ) :=
        lt_of_le_of_lt (div_nonneg hk0 (le_of_lt hδ)) hn
      exact Nat.cast_pos.mp hnn
    have hn1 : 1 ≤ n := hn0
    have hnS : (k : ℝ) - 1 < (n : ℝ) * (S - 1) := by
      have h := (div_lt_iff₀ hδ).mp hn
      linarith
    have hceil := ceil_sum k α hαpos hαlt hdisj hcover n hn1
    have hcast : ((∑ i : Fin k, ⌈(n : ℝ) * α i⌉ : ℤ) : ℝ) = (n : ℝ) + (k : ℝ) - 1 := by
      exact_mod_cast hceil
    have hlb := (hbnds n hn1).1
    rw [hcast] at hlb
    nlinarith

-- The complementary sum: ∑ (⌈Mαᵢ⌉ - Mαᵢ) = k - 1.
private theorem tsum (k : ℕ) (α : Fin k → ℝ)
    (hαpos : ∀ i, 0 < α i) (hαlt : ∀ i, α i < 1)
    (hdisj : (Set.univ : Set (Fin k)).PairwiseDisjoint
      (fun i => {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}))
    (hcover : (⋃ i, {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}) =
      {x : ℤ | 0 < x})
    (hS : ∑ i : Fin k, α i = 1)
    (M : ℕ) (hM : 1 ≤ M) :
    ∑ i : Fin k, (((⌈(M : ℝ) * α i⌉ : ℤ) : ℝ) - (M : ℝ) * α i) = (k : ℝ) - 1 := by
  have hceil := ceil_sum k α hαpos hαlt hdisj hcover M hM
  have h1 : ∑ i : Fin k, (((⌈(M : ℝ) * α i⌉ : ℤ) : ℝ) - (M : ℝ) * α i) =
      ((∑ i : Fin k, ⌈(M : ℝ) * α i⌉ : ℤ) : ℝ) - (M : ℝ) * ∑ i : Fin k, α i := by
    rw [Int.cast_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [h1, hS]
  have h2 : ((∑ i : Fin k, ⌈(M : ℝ) * α i⌉ : ℤ) : ℝ) = (M : ℝ) + (k : ℝ) - 1 := by
    exact_mod_cast hceil
  linarith

-- No multiple of any αᵢ is an integer.
private theorem fract_ne_zero (k : ℕ) (α : Fin k → ℝ)
    (hαpos : ∀ i, 0 < α i) (hαlt : ∀ i, α i < 1)
    (hdisj : (Set.univ : Set (Fin k)).PairwiseDisjoint
      (fun i => {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}))
    (hcover : (⋃ i, {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}) =
      {x : ℤ | 0 < x})
    (hk2 : 2 ≤ k) (hS : ∑ i : Fin k, α i = 1)
    (M : ℕ) (hM : 1 ≤ M) (i : Fin k) :
    Int.fract ((M : ℝ) * α i) ≠ 0 := by
  intro hz
  have hx0 : ((⌈(M : ℝ) * α i⌉ : ℤ) : ℝ) = (M : ℝ) * α i := by
    have hfl : ((⌊(M : ℝ) * α i⌋ : ℤ) : ℝ) = (M : ℝ) * α i := by
      have hff := Int.floor_add_fract ((M : ℝ) * α i)
      rw [hz] at hff
      linarith
    have hceil : ⌈(M : ℝ) * α i⌉ = ⌊(M : ℝ) * α i⌋ := by
      have hcc : ⌈(((⌊(M : ℝ) * α i⌋ : ℤ)) : ℝ)⌉ = ⌊(M : ℝ) * α i⌋ :=
        Int.ceil_intCast _
      rwa [hfl] at hcc
    rw [hceil]
    exact hfl
  have htsum := tsum k α hαpos hαlt hdisj hcover hS M hM
  have hti : ((⌈(M : ℝ) * α i⌉ : ℤ) : ℝ) - (M : ℝ) * α i = 0 := by linarith [hx0]
  have hrest : ∑ j ∈ Finset.univ.erase i,
      (((⌈(M : ℝ) * α j⌉ : ℤ) : ℝ) - (M : ℝ) * α j) = (k : ℝ) - 1 := by
    have hsplit := Finset.sum_erase_add Finset.univ
      (fun j => ((⌈(M : ℝ) * α j⌉ : ℤ) : ℝ) - (M : ℝ) * α j) (Finset.mem_univ i)
    linarith [htsum, hti]
  have hlt : ∑ j ∈ Finset.univ.erase i,
      (((⌈(M : ℝ) * α j⌉ : ℤ) : ℝ) - (M : ℝ) * α j) < (k : ℝ) - 1 := by
    have hle1 : ∑ j ∈ Finset.univ.erase i,
        (((⌈(M : ℝ) * α j⌉ : ℤ) : ℝ) - (M : ℝ) * α j) <
        ∑ j ∈ Finset.univ.erase i, (1 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro j _
        have h := Int.ceil_lt_add_one ((M : ℝ) * α j)
        linarith
      · have hcard : 1 ≤ (Finset.univ.erase i).card := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
            Fintype.card_fin]
          omega
        obtain ⟨j0, hj0⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.erase i).card)
        exact ⟨j0, hj0, by
          have h := Int.ceil_lt_add_one ((M : ℝ) * α j0)
          linarith⟩
    have heq1 : (∑ j ∈ Finset.univ.erase i, (1 : ℝ)) = (k : ℝ) - 1 := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
        Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    linarith
  linarith [hrest, hlt]

-- Ceil from floor for non-integers.
private theorem ceil_eq_floor_succ (x : ℝ) (hx : Int.fract x ≠ 0) : ⌈x⌉ = ⌊x⌋ + 1 := by
  rw [Int.ceil_eq_iff]
  constructor
  · have hpos : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hx)
    have hff := Int.floor_add_fract x
    push_cast
    linarith
  · have hlt := Int.fract_lt_one x
    have hff := Int.floor_add_fract x
    push_cast
    linarith

-- Fractional parts sum to 1.
private theorem fract_sum (k : ℕ) (α : Fin k → ℝ)
    (hαpos : ∀ i, 0 < α i) (hαlt : ∀ i, α i < 1)
    (hdisj : (Set.univ : Set (Fin k)).PairwiseDisjoint
      (fun i => {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}))
    (hcover : (⋃ i, {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}) =
      {x : ℤ | 0 < x})
    (hk2 : 2 ≤ k) (hS : ∑ i : Fin k, α i = 1)
    (M : ℕ) (hM : 1 ≤ M) :
    ∑ i : Fin k, Int.fract ((M : ℝ) * α i) = 1 := by
  have htsum := tsum k α hαpos hαlt hdisj hcover hS M hM
  have hterm : ∀ i : Fin k, ((⌈(M : ℝ) * α i⌉ : ℤ) : ℝ) - (M : ℝ) * α i =
      1 - Int.fract ((M : ℝ) * α i) := by
    intro i
    have hne := fract_ne_zero k α hαpos hαlt hdisj hcover hk2 hS M hM i
    have hce := ceil_eq_floor_succ ((M : ℝ) * α i) hne
    have hceR : ((⌈(M : ℝ) * α i⌉ : ℤ) : ℝ) = ((⌊(M : ℝ) * α i⌋ : ℤ) : ℝ) + 1 := by
      exact_mod_cast hce
    have hff := Int.floor_add_fract ((M : ℝ) * α i)
    linarith
  calc ∑ i : Fin k, Int.fract ((M : ℝ) * α i)
      = (k : ℝ) - ∑ i : Fin k, (((⌈(M : ℝ) * α i⌉ : ℤ) : ℝ) - (M : ℝ) * α i) := by
        have hcongr : ∑ i : Fin k, (((⌈(M : ℝ) * α i⌉ : ℤ) : ℝ) - (M : ℝ) * α i) =
            ∑ i : Fin k, (1 - Int.fract ((M : ℝ) * α i)) :=
          Finset.sum_congr rfl (fun i _ => hterm i)
        rw [hcongr, Finset.sum_sub_distrib]
        have hone : (∑ _x : Fin k, (1 : ℝ)) = (k : ℝ) := by simp
        rw [hone]
        ring
    _ = 1 := by rw [htsum]; ring

-- Floor-sum identity.
private theorem floor_sum (k : ℕ) (α : Fin k → ℝ)
    (hαpos : ∀ i, 0 < α i) (hαlt : ∀ i, α i < 1)
    (hdisj : (Set.univ : Set (Fin k)).PairwiseDisjoint
      (fun i => {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}))
    (hcover : (⋃ i, {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}) =
      {x : ℤ | 0 < x})
    (hk2 : 2 ≤ k) (hS : ∑ i : Fin k, α i = 1)
    (N : ℕ) (hN : 1 ≤ N) :
    ∑ i : Fin k, ⌊(N : ℝ) * α i⌋ = (N : ℤ) - 1 := by
  have hceil := ceil_sum k α hαpos hαlt hdisj hcover N hN
  have hfl : ∀ i : Fin k, ⌊(N : ℝ) * α i⌋ = ⌈(N : ℝ) * α i⌉ - 1 := by
    intro i
    have hne := fract_ne_zero k α hαpos hαlt hdisj hcover hk2 hS N hN i
    have hce := ceil_eq_floor_succ ((N : ℝ) * α i) hne
    omega
  calc ∑ i : Fin k, ⌊(N : ℝ) * α i⌋
      = ∑ i : Fin k, (⌈(N : ℝ) * α i⌉ - 1) :=
        Finset.sum_congr rfl (fun i _ => hfl i)
    _ = (∑ i : Fin k, ⌈(N : ℝ) * α i⌉) - (k : ℤ) := by
        rw [Finset.sum_sub_distrib]
        have hone : (∑ _x : Fin k, (1 : ℤ)) = (k : ℤ) := by simp
        rw [hone]
    _ = (N : ℤ) - 1 := by rw [hceil]; ring

-- Consecutive floor-sums differ by exactly 1 in total.
private theorem carry_sum (k : ℕ) (α : Fin k → ℝ)
    (hαpos : ∀ i, 0 < α i) (hαlt : ∀ i, α i < 1)
    (hdisj : (Set.univ : Set (Fin k)).PairwiseDisjoint
      (fun i => {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}))
    (hcover : (⋃ i, {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}) =
      {x : ℤ | 0 < x})
    (hk2 : 2 ≤ k) (hS : ∑ i : Fin k, α i = 1)
    (N : ℕ) (hN : 1 ≤ N) :
    ∑ i : Fin k, (⌊((N : ℝ) + 1) * α i⌋ - ⌊(N : ℝ) * α i⌋) = 1 := by
  have hH1 := floor_sum k α hαpos hαlt hdisj hcover hk2 hS (N + 1) (by omega)
  have hH0 := floor_sum k α hαpos hαlt hdisj hcover hk2 hS N hN
  rw [Finset.sum_sub_distrib]
  have eR : ((N : ℝ) + 1) = (((N + 1 : ℕ)) : ℝ) := by push_cast; ring
  have eZ : (((N + 1 : ℕ)) : ℤ) = (N : ℤ) + 1 := by push_cast; ring
  rw [eR, hH1, hH0, eZ]
  omega

-- Two distinct indices cannot both carry.
private theorem carry_unique (k : ℕ) (α : Fin k → ℝ)
    (hαpos : ∀ i, 0 < α i) (hαlt : ∀ i, α i < 1)
    (hdisj : (Set.univ : Set (Fin k)).PairwiseDisjoint
      (fun i => {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}))
    (hcover : (⋃ i, {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}) =
      {x : ℤ | 0 < x})
    (hk2 : 2 ≤ k) (hS : ∑ i : Fin k, α i = 1)
    (N : ℕ) (hN : 1 ≤ N) (a b : Fin k) (hab : a ≠ b)
    (ha : ⌊((N : ℝ) + 1) * α a⌋ - ⌊(N : ℝ) * α a⌋ = 1)
    (hb : ⌊((N : ℝ) + 1) * α b⌋ - ⌊(N : ℝ) * α b⌋ = 1) : False := by
  have hcs := carry_sum k α hαpos hαlt hdisj hcover hk2 hS N hN
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      0 ≤ ⌊((N : ℝ) + 1) * α i⌋ - ⌊(N : ℝ) * α i⌋ := by
    intro i _
    have hle : ⌊(N : ℝ) * α i⌋ ≤ ⌊((N : ℝ) + 1) * α i⌋ := by
      apply Int.floor_le_floor
      have hNle : (N : ℝ) ≤ (N : ℝ) + 1 := le_add_of_nonneg_right zero_le_one
      exact mul_le_mul_of_nonneg_right hNle (le_of_lt (hαpos i))
    omega
  have hsd : ∑ i ∈ ({a, b} : Finset (Fin k)),
      (⌊((N : ℝ) + 1) * α i⌋ - ⌊(N : ℝ) * α i⌋) ≤
      ∑ i ∈ Finset.univ,
      (⌊((N : ℝ) + 1) * α i⌋ - ⌊(N : ℝ) * α i⌋) := by
    have hsub : ({a, b} : Finset (Fin k)) ⊆ Finset.univ := Finset.subset_univ _
    have hsdiff := Finset.sum_sdiff hsub
      (f := fun i => ⌊((N : ℝ) + 1) * α i⌋ - ⌊(N : ℝ) * α i⌋)
    have hnn : 0 ≤ ∑ i ∈ Finset.univ \ {a, b},
        (⌊((N : ℝ) + 1) * α i⌋ - ⌊(N : ℝ) * α i⌋) :=
      Finset.sum_nonneg (fun i _ => hnonneg i (Finset.mem_univ i))
    linarith
  rw [Finset.sum_pair hab, ha, hb] at hsd
  omega

/-- **Uspensky's theorem on Beatty partitions.** For a real number $\alpha$ with
$0 < \alpha < 1$, let $B_\alpha = \{\lfloor n/\alpha \rfloor : n \text{ an integer}, n \ge 1\}$
be its Beatty sequence. Let $k \ge 3$ and let $\alpha_1, \dots, \alpha_k$ be real numbers with
$0 < \alpha_i < 1$ for every $i$. Then $B_{\alpha_1}, \dots, B_{\alpha_k}$ do not partition the
positive integers: it is not the case both that $B_{\alpha_i} \cap B_{\alpha_j} = \emptyset$
for all $i \ne j$ and that $B_{\alpha_1} \cup \dots \cup B_{\alpha_k} = \{1, 2, 3, \dots\}$.

No irrationality hypothesis is imposed on the $\alpha_i$.

Source: A. J. Hildebrand, Xiaomin Li, Junxian Li, and Yun Xie, *Almost Beatty
Partitions*, Journal of Integer Sequences 22 (2019), Article 19.4.6, Theorem B
(Uspensky's theorem), lines 234–236,
<https://cs.uwaterloo.ca/journals/JIS/VOL22/Hildebrand/hilde2.tex>;
first proved by Uspensky in 1927 (lines 238–244).
-/
theorem uspensky_no_partition_into_three_or_more_beatty_sequences
    (k : ℕ) (hk : 3 ≤ k) (α : Fin k → ℝ)
    (hαpos : ∀ i, 0 < α i) (hαlt : ∀ i, α i < 1) :
    ¬ ((Set.univ : Set (Fin k)).PairwiseDisjoint
        (fun i => {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}) ∧
      (⋃ i, {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}) =
        {x : ℤ | 0 < x}) := by
  rintro ⟨hdisj, hcover⟩
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hS : ∑ i : Fin k, α i = 1 := sum_alpha k α hαpos hαlt hdisj hcover hk1
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨i₀, _, hmin⟩ := Finset.exists_min_image Finset.univ α hne
  have hmin' : ∀ j : Fin k, α i₀ ≤ α j := fun j => hmin j (Finset.mem_univ j)
  have hkm : (k : ℝ) * α i₀ ≤ 1 := by
    have hconst : (k : ℝ) * α i₀ = ∑ _i : Fin k, α i₀ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hconst]
    calc ∑ _i : Fin k, α i₀ ≤ ∑ i : Fin k, α i :=
          Finset.sum_le_sum (fun j _ => hmin' j)
      _ = 1 := hS
  have h3mu : 3 * α i₀ ≤ 1 := by
    have h1 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h2 : (3 : ℝ) * α i₀ ≤ (k : ℝ) * α i₀ :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt (hαpos i₀))
    linarith
  have hMpos0 : (0 : ℝ) ≤ 1 / α i₀ := le_of_lt (one_div_pos.mpr (hαpos i₀))
  set M := ⌊1 / α i₀⌋₊ with hMdef
  have hM3 : 3 ≤ M := by
    rw [hMdef, Nat.le_floor_iff hMpos0, le_div_iff₀ (hαpos i₀)]
    push_cast
    linarith [h3mu]
  have hM1 : 1 ≤ M := by omega
  have hMle : (M : ℝ) ≤ 1 / α i₀ := by
    rw [hMdef]
    exact Nat.floor_le hMpos0
  have hMgt : (1 : ℝ) / α i₀ < (M : ℝ) + 1 := by
    rw [hMdef]
    exact Nat.lt_floor_add_one _
  have hMmule : (M : ℝ) * α i₀ ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_right hMle (le_of_lt (hαpos i₀))
    have hba : (1 : ℝ) / α i₀ * α i₀ = 1 := one_div_mul_cancel (ne_of_gt (hαpos i₀))
    linarith
  have hMlt1 : (M : ℝ) * α i₀ < 1 := by
    by_contra hle
    have hle' : (1 : ℝ) ≤ (M : ℝ) * α i₀ := not_lt.mp hle
    have heq : (M : ℝ) * α i₀ = 1 := le_antisymm hMmule hle'
    have hz := fract_ne_zero k α hαpos hαlt hdisj hcover hk2 hS M hM1 i₀
    rw [heq] at hz
    simp at hz
  have hMgt' : 1 - α i₀ < (M : ℝ) * α i₀ := by
    have hmul := mul_lt_mul_of_pos_right hMgt (hαpos i₀)
    have hba : (1 : ℝ) / α i₀ * α i₀ = 1 := one_div_mul_cancel (ne_of_gt (hαpos i₀))
    rw [hba] at hmul
    have hexpand : ((M : ℝ) + 1) * α i₀ = (M : ℝ) * α i₀ + α i₀ := by ring
    linarith
  have hfr : Int.fract ((M : ℝ) * α i₀) = (M : ℝ) * α i₀ := by
    rw [Int.fract_eq_self]
    constructor
    · have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
      exact mul_nonneg hMnn (le_of_lt (hαpos i₀))
    · exact hMlt1
  have hfsum := fract_sum k α hαpos hαlt hdisj hcover hk2 hS M hM1
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun j => Int.fract ((M : ℝ) * α j)) (Finset.mem_univ i₀)
  simp only [hfr, hfsum] at hsplit
  have hsmall : ∑ j ∈ Finset.univ.erase i₀, Int.fract ((M : ℝ) * α j) < α i₀ := by
    linarith [hMgt']
  have hlt : ∀ j : Fin k, j ≠ i₀ → Int.fract ((M : ℝ) * α j) < α j := by
    intro j hj
    have hmem : j ∈ Finset.univ.erase i₀ := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
    have hle := Finset.single_le_sum (fun j _ => Int.fract_nonneg ((M : ℝ) * α j)) hmem
    have hjle : α i₀ ≤ α j := hmin' j
    linarith
  have hN1 : 1 ≤ M - 1 := by omega
  have eM : (M : ℝ) = (((M - 1 : ℕ)) : ℝ) + 1 := by
    rw [Nat.cast_sub hM1]; ring
  have hcarry : ∀ j : Fin k, j ≠ i₀ →
      ⌊(M : ℝ) * α j⌋ - ⌊(((M - 1 : ℕ)) : ℝ) * α j⌋ = 1 := by
    intro j hj
    have h01 : ⌊(M : ℝ) * α j⌋ - ⌊(((M - 1 : ℕ)) : ℝ) * α j⌋ = 0 ∨
        ⌊(M : ℝ) * α j⌋ - ⌊(((M - 1 : ℕ)) : ℝ) * α j⌋ = 1 := by
      have hle1 : ⌊(((M - 1 : ℕ)) : ℝ) * α j⌋ ≤ ⌊(M : ℝ) * α j⌋ := by
        apply Int.floor_le_floor
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (hαpos j))
        have hleM : (((M - 1 : ℕ)) : ℝ) ≤ (M : ℝ) := by
          rw [Nat.cast_sub hM1]; linarith
        exact hleM
      have hle2 : ⌊(M : ℝ) * α j⌋ ≤ ⌊(((M - 1 : ℕ)) : ℝ) * α j⌋ + 1 := by
        have heq : (M : ℝ) * α j = (((M - 1 : ℕ)) : ℝ) * α j + α j := by
          rw [eM]; ring
        rw [heq]
        have hle : (((M - 1 : ℕ)) : ℝ) * α j + α j ≤ (((M - 1 : ℕ)) : ℝ) * α j + 1 := by
          linarith [hαlt j]
        have hfl := Int.floor_le_floor hle
        rwa [Int.floor_add_one] at hfl
      omega
    rcases h01 with h0 | h1
    · exfalso
      have hd0 : ⌊(M : ℝ) * α j⌋ = ⌊(((M - 1 : ℕ)) : ℝ) * α j⌋ := by omega
      have hd0R : ((⌊(M : ℝ) * α j⌋ : ℤ) : ℝ) =
          ((⌊((((M - 1 : ℕ)) : ℝ)) * α j⌋ : ℤ) : ℝ) := by
        exact_mod_cast hd0
      have hffM := Int.floor_add_fract ((M : ℝ) * α j)
      have hffN := Int.floor_add_fract ((((M - 1 : ℕ)) : ℝ) * α j)
      have heq : (M : ℝ) * α j = (((M - 1 : ℕ)) : ℝ) * α j + α j := by
        rw [eM]; ring
      have hnn := Int.fract_nonneg ((((M - 1 : ℕ)) : ℝ) * α j)
      have hge : α j ≤ Int.fract ((M : ℝ) * α j) := by linarith
      linarith [hlt j hj, hge]
    · exact h1
  have hcard2 : 2 ≤ (Finset.univ.erase i₀).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, haE, b, hbE, hab⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.erase i₀).card)
  have hai₀ : a ≠ i₀ := (Finset.mem_erase.mp haE).1
  have hbi₀ : b ≠ i₀ := (Finset.mem_erase.mp hbE).1
  have ha1 := hcarry a hai₀
  have hb1 := hcarry b hbi₀
  rw [eM] at ha1 hb1
  exact carry_unique k α hαpos hαlt hdisj hcover hk2 hS (M - 1) hN1 a b hab ha1 hb1

end

end MetaMathlibExt
