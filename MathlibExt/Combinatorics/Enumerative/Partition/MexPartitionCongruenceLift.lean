/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic

import Mathlib.Tactic.Ring

/-!
# Lifting partition congruences to mex partition functions

This file proves the Barman-Singh lift by removing the forced parts preceding a partition's
minimal excludant and then summing the resulting exact-mex fibers.
-/

@[expose] public section

namespace MetaMathlibExt

private theorem mex_exists_missing {N : ℕ} (c : ℕ → ℕ) (hc : StrictMono c)
    (p : Nat.Partition N) : ∃ j, c j ∉ p.parts := by
  refine ⟨N + 1, ?_⟩
  intro hmem
  have hle := Nat.Partition.le_of_mem_parts hmem
  have hself : N + 1 ≤ c (N + 1) := hc.le_apply
  omega

private noncomputable def mex_index {N : ℕ} (c : ℕ → ℕ) (hc : StrictMono c)
    (p : Nat.Partition N) : ℕ :=
  Nat.find (mex_exists_missing c hc p)

private theorem mex_index_not_mem {N : ℕ} (c : ℕ → ℕ) (hc : StrictMono c)
    (p : Nat.Partition N) : c (mex_index c hc p) ∉ p.parts := by
  exact Nat.find_spec (mex_exists_missing c hc p)

private theorem mex_index_mem_of_lt {N : ℕ} (c : ℕ → ℕ) (hc : StrictMono c)
    (p : Nat.Partition N) {i : ℕ} (hi : i < mex_index c hc p) : c i ∈ p.parts := by
  by_contra hmem
  unfold mex_index at hi
  exact (Nat.not_le_of_gt hi) (Nat.find_min' (mex_exists_missing c hc p) hmem)

private theorem mex_index_le {N : ℕ} (c : ℕ → ℕ) (hc : StrictMono c)
    (p : Nat.Partition N) : mex_index c hc p ≤ N + 1 := by
  apply Nat.find_min' (mex_exists_missing c hc p)
  intro hmem
  have hle := Nat.Partition.le_of_mem_parts hmem
  have hself : N + 1 ≤ c (N + 1) := hc.le_apply
  omega

private def mex_prefix (c : ℕ → ℕ) (j : ℕ) : Multiset ℕ :=
  (Finset.image c (Finset.range j)).val

private theorem mex_prefix_le_iff {N : ℕ} (c : ℕ → ℕ) (j : ℕ)
    (p : Nat.Partition N) :
    mex_prefix c j ≤ p.parts ↔ ∀ i < j, c i ∈ p.parts := by
  have hnodup : (mex_prefix c j).Nodup := (Finset.image c (Finset.range j)).nodup
  rw [Multiset.le_iff_subset hnodup]
  constructor
  · intro h i hi
    apply h
    simp only [mex_prefix, Finset.mem_val, Finset.mem_image, Finset.mem_range]
    exact ⟨i, hi, rfl⟩
  · intro h x hx
    simp only [mex_prefix, Finset.mem_val, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i hi

private theorem mex_prefix_pos (c : ℕ → ℕ) (hcpos : ∀ i, 0 < c i) (j : ℕ) :
    ∀ x ∈ mex_prefix c j, 0 < x := by
  intro x hx
  simp only [mex_prefix, Finset.mem_val, Finset.mem_image] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact hcpos i

private theorem mex_prefix_sum (c : ℕ → ℕ) (hc : Function.Injective c) (j : ℕ) :
    (mex_prefix c j).sum = ∑ i ∈ Finset.range j, c i := by
  rw [mex_prefix, Finset.sum_val]
  exact Finset.sum_image (Set.injOn_of_injective hc)

private theorem mex_prefix_succ_le_iff {N : ℕ} (c : ℕ → ℕ) (j : ℕ)
    (p : Nat.Partition N) :
    mex_prefix c (j + 1) ≤ p.parts ↔ mex_prefix c j ≤ p.parts ∧ c j ∈ p.parts := by
  rw [mex_prefix_le_iff, mex_prefix_le_iff]
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h j (by omega)⟩
  · rintro ⟨h, hj⟩ i hi
    by_cases hij : i < j
    · exact h i hij
    · have : i = j := by omega
      subst i
      exact hj

private theorem mex_index_eq_iff {N : ℕ} (c : ℕ → ℕ) (hc : StrictMono c)
    (p : Nat.Partition N) (j : ℕ) :
    mex_index c hc p = j ↔ mex_prefix c j ≤ p.parts ∧ c j ∉ p.parts := by
  constructor
  · intro h
    subst j
    refine ⟨(mex_prefix_le_iff c _ p).2 ?_, mex_index_not_mem c hc p⟩
    exact fun i hi => mex_index_mem_of_lt c hc p hi
  · rintro ⟨hprefix, hmissing⟩
    have hle : mex_index c hc p ≤ j := by
      unfold mex_index
      exact Nat.find_min' (mex_exists_missing c hc p) hmissing
    have hnot : ¬mex_index c hc p < j := by
      intro hlt
      exact (mex_index_not_mem c hc p) ((mex_prefix_le_iff c j p).1 hprefix _ hlt)
    exact Nat.le_antisymm hle (Nat.not_lt.mp hnot)

private def mex_remove_equiv {N : ℕ} (R : Multiset ℕ)
    (hpos : ∀ x ∈ R, 0 < x) (hsum : R.sum ≤ N) :
    {p : Nat.Partition N // R ≤ p.parts} ≃ Nat.Partition (N - R.sum) where
  toFun p :=
    ⟨p.1.parts - R,
      by
        intro x hi
        exact p.1.parts_pos (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi),
      by
        have hcancel := Multiset.sub_add_cancel p.2
        have hs := congrArg Multiset.sum hcancel
        rw [Multiset.sum_add, p.1.parts_sum] at hs
        omega⟩
  invFun q :=
    ⟨⟨q.parts + R,
      by
        intro x hx
        rw [Multiset.mem_add] at hx
        rcases hx with hx | hx
        · exact q.parts_pos hx
        · exact hpos x hx,
      by
        rw [Multiset.sum_add, q.parts_sum]
        omega⟩,
      Multiset.le_add_left R q.parts⟩
  left_inv p := by
    apply Subtype.ext
    apply Nat.Partition.ext
    exact Multiset.sub_add_cancel p.2
  right_inv q := by
    apply Nat.Partition.ext
    exact Multiset.add_sub_cancel_right

private theorem mex_required_card_dvd (m a b n T : ℕ) (hb : b < a)
    (hbase : ∀ q : ℕ, m ∣ Fintype.card (Nat.Partition (a * q + b)))
    (R : Multiset ℕ) (hpos : ∀ x ∈ R, 0 < x) (hsum : R.sum = a * T) :
    m ∣ (Finset.univ.filter fun p : Nat.Partition (a * n + b) => R ≤ p.parts).card := by
  classical
  by_cases hT : T ≤ n
  · have hmul : a * T ≤ a * n := Nat.mul_le_mul_left a hT
    have hRle : R.sum ≤ a * n + b := by
      rw [hsum]
      omega
    have hindex : a * n + b - R.sum = a * (n - T) + b := by
      rw [hsum, Nat.sub_add_comm hmul, ← Nat.mul_sub_left_distrib]
    have hcard :
        (Finset.univ.filter fun p : Nat.Partition (a * n + b) => R ≤ p.parts).card =
          Fintype.card (Nat.Partition (a * n + b - R.sum)) := by
      calc
        _ = Fintype.card {p : Nat.Partition (a * n + b) // R ≤ p.parts} :=
          (Fintype.card_subtype _).symm
        _ = _ := Fintype.card_congr (mex_remove_equiv R hpos hRle)
    rw [hcard, hindex]
    exact hbase (n - T)
  · have hnT : n < T := Nat.lt_of_not_ge hT
    have hNlt : a * n + b < R.sum := by
      calc
        a * n + b < a * n + a := Nat.add_lt_add_left hb _
        _ = a * (n + 1) := by ring
        _ ≤ a * T := Nat.mul_le_mul_left a (by omega)
        _ = R.sum := hsum.symm
    have hempty :
        (Finset.univ.filter fun p : Nat.Partition (a * n + b) => R ≤ p.parts) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      have hR := (Finset.mem_filter.mp hp).2
      have hcancel := Multiset.sub_add_cancel hR
      have hs := congrArg Multiset.sum hcancel
      rw [Multiset.sum_add, p.parts_sum] at hs
      omega
    simp [hempty]

private theorem mex_fiber_add_prefix_card {N : ℕ} (c : ℕ → ℕ)
    (hc : StrictMono c) (j : ℕ) :
    (Finset.univ.filter fun p : Nat.Partition N => mex_index c hc p = j).card +
        (Finset.univ.filter fun p : Nat.Partition N => mex_prefix c (j + 1) ≤ p.parts).card =
      (Finset.univ.filter fun p : Nat.Partition N => mex_prefix c j ≤ p.parts).card := by
  classical
  have hfiber :
      (Finset.univ.filter fun p : Nat.Partition N => mex_index c hc p = j) =
        (Finset.univ.filter fun p : Nat.Partition N => mex_prefix c j ≤ p.parts).filter
          fun p => c j ∉ p.parts := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact mex_index_eq_iff c hc p j
  have hnext :
      (Finset.univ.filter fun p : Nat.Partition N => mex_prefix c (j + 1) ≤ p.parts) =
        (Finset.univ.filter fun p : Nat.Partition N => mex_prefix c j ≤ p.parts).filter
          fun p => c j ∈ p.parts := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact mex_prefix_succ_le_iff c j p
  rw [hfiber, hnext]
  simpa only [not_not] using
    (Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun p : Nat.Partition N => mex_prefix c j ≤ p.parts)
      (fun p => c j ∉ p.parts))

private theorem mex_fiber_card_dvd (m a b n : ℕ) (hb : b < a)
    (hbase : ∀ q : ℕ, m ∣ Fintype.card (Nat.Partition (a * q + b)))
    (c : ℕ → ℕ) (hc : StrictMono c) (hcpos : ∀ i, 0 < c i) (T : ℕ → ℕ)
    (hsum : ∀ j, (mex_prefix c j).sum = a * T j) (j : ℕ) :
    m ∣ (Finset.univ.filter fun p : Nat.Partition (a * n + b) =>
      mex_index c hc p = j).card := by
  have hprefix := mex_required_card_dvd m a b n (T j) hb hbase (mex_prefix c j)
    (mex_prefix_pos c hcpos j) (hsum j)
  have hnext := mex_required_card_dvd m a b n (T (j + 1)) hb hbase
    (mex_prefix c (j + 1)) (mex_prefix_pos c hcpos (j + 1)) (hsum (j + 1))
  have hadd : m ∣
      (Finset.univ.filter fun p : Nat.Partition (a * n + b) =>
        mex_index c hc p = j).card +
      (Finset.univ.filter fun p : Nat.Partition (a * n + b) =>
        mex_prefix c (j + 1) ≤ p.parts).card := by
    rw [mex_fiber_add_prefix_card c hc j]
    exact hprefix
  exact (Nat.dvd_add_iff_left hnext).mpr hadd

private theorem mex_even_index_card_dvd (m a b n : ℕ) (hb : b < a)
    (hbase : ∀ q : ℕ, m ∣ Fintype.card (Nat.Partition (a * q + b)))
    (c : ℕ → ℕ) (hc : StrictMono c) (hcpos : ∀ i, 0 < c i) (T : ℕ → ℕ)
    (hsum : ∀ j, (mex_prefix c j).sum = a * T j) :
    m ∣ (Finset.univ.filter fun p : Nat.Partition (a * n + b) =>
      Even (mex_index c hc p)).card := by
  classical
  have hfilter :
      (Finset.univ.filter fun p : Nat.Partition (a * n + b) =>
        Even (mex_index c hc p)) =
      (Finset.univ.filter fun p : Nat.Partition (a * n + b) =>
        mex_index c hc p ∈ (Finset.range (a * n + b + 2)).filter Even) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · intro heven
      exact ⟨by have := mex_index_le c hc p; omega, heven⟩
    · rintro ⟨-, heven⟩
      exact heven
  have hfibers := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Nat.Partition (a * n + b)))
    ((Finset.range (a * n + b + 2)).filter Even) (mex_index c hc)
  rw [hfilter, ← hfibers]
  apply Finset.dvd_sum
  intro j hj
  exact mex_fiber_card_dvd m a b n hb hbase c hc hcpos T hsum j

private theorem mex_target_iff_even_index {N : ℕ} (c : ℕ → ℕ)
    (hc : StrictMono c) (Q S : ℕ → Prop)
    (hQ : ∀ x, 0 < x ∧ Q x ↔ ∃ j, x = c j) (hS : ∀ j, S (c j) ↔ Even j)
    (p : Nat.Partition N) :
    (∃ μ, 0 < μ ∧ Q μ ∧ μ ∉ p.parts ∧
      (∀ k, 0 < k → k < μ → Q k → k ∈ p.parts) ∧ S μ) ↔
      Even (mex_index c hc p) := by
  constructor
  · rintro ⟨μ, hμpos, hQμ, hmissing, hbelow, hselected⟩
    obtain ⟨j, rfl⟩ := (hQ μ).mp ⟨hμpos, hQμ⟩
    have hle : mex_index c hc p ≤ j := by
      unfold mex_index
      exact Nat.find_min' (mex_exists_missing c hc p) hmissing
    have hge : j ≤ mex_index c hc p := by
      apply Nat.not_lt.mp
      intro hlt
      have hcand := (hQ _).mpr ⟨mex_index c hc p, rfl⟩
      have hmem := hbelow (c (mex_index c hc p)) hcand.1 (hc hlt) hcand.2
      exact (mex_index_not_mem c hc p) hmem
    have heq : mex_index c hc p = j := Nat.le_antisymm hle hge
    rw [heq]
    exact (hS j).mp hselected
  · intro heven
    have hcand := (hQ _).mpr ⟨mex_index c hc p, rfl⟩
    refine ⟨c (mex_index c hc p), hcand.1, hcand.2, mex_index_not_mem c hc p,
      ?_, (hS _).mpr heven⟩
    intro k hkpos hklt hkQ
    obtain ⟨i, rfl⟩ := (hQ k).mp ⟨hkpos, hkQ⟩
    exact mex_index_mem_of_lt c hc p ((hc.lt_iff_lt).mp hklt)

private def mex_linear_candidate (A i : ℕ) : ℕ := A * (i + 1)

private def mex_odd_candidate (A i : ℕ) : ℕ := A * (2 * i + 1)

private theorem mex_linear_candidate_strict (A : ℕ) (hA : 0 < A) :
    StrictMono (mex_linear_candidate A) := by
  intro i j hij
  apply Nat.mul_lt_mul_of_pos_left _ hA
  omega

private theorem mex_odd_candidate_strict (A : ℕ) (hA : 0 < A) :
    StrictMono (mex_odd_candidate A) := by
  intro i j hij
  apply Nat.mul_lt_mul_of_pos_left _ hA
  omega

private theorem mex_linear_candidate_pos (A : ℕ) (hA : 0 < A) (i : ℕ) :
    0 < mex_linear_candidate A i := by
  exact Nat.mul_pos hA (by omega)

private theorem mex_odd_candidate_pos (A : ℕ) (hA : 0 < A) (i : ℕ) :
    0 < mex_odd_candidate A i := by
  exact Nat.mul_pos hA (by omega)

private theorem mex_scaled_prefix_sum (a t : ℕ) (d : ℕ → ℕ)
    (hc : StrictMono fun i => (a * t) * d i) (j : ℕ) :
    (mex_prefix (fun i => (a * t) * d i) j).sum =
      a * (t * ∑ i ∈ Finset.range j, d i) := by
  rw [mex_prefix_sum _ hc.injective, ← Finset.mul_sum]
  simp only [mul_assoc]

private theorem mex_linear_candidate_iff (A μ : ℕ) (hA : 0 < A) :
    (0 < μ ∧ μ % A = A % A) ↔ ∃ j, μ = mex_linear_candidate A j := by
  rw [Nat.mod_self]
  constructor
  · rintro ⟨hμ, hmod⟩
    obtain ⟨q, rfl⟩ := (Nat.dvd_iff_mod_eq_zero.mpr hmod)
    have hq : q ≠ 0 := by
      intro hq
      subst q
      simp at hμ
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    exact ⟨j, by simp [mex_linear_candidate]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨mex_linear_candidate_pos A hA j, by simp [mex_linear_candidate]⟩

private theorem mex_linear_selected_iff (A j : ℕ) (hA : 0 < A) :
    mex_linear_candidate A j % (2 * A) = A % (2 * A) ↔ Even j := by
  have hlt : A < 2 * A := by
    calc
      A = A * 1 := by simp
      _ < A * 2 := (Nat.mul_lt_mul_left hA).2 (by omega)
      _ = 2 * A := by ac_rfl
  have hleft : mex_linear_candidate A j % (2 * A) = A * ((j + 1) % 2) := by
    rw [mex_linear_candidate, mul_comm 2 A]
    exact Nat.mul_mod_mul_left A (j + 1) 2
  rw [hleft, Nat.mod_eq_of_lt hlt]
  have hcancel : A * ((j + 1) % 2) = A ↔ (j + 1) % 2 = 1 := by
    simpa only [mul_one] using
      (Nat.mul_left_cancel_iff hA (m := (j + 1) % 2) (k := 1))
  rw [hcancel, Nat.even_iff]
  omega

private theorem mex_odd_candidate_iff (A μ : ℕ) (hA : 0 < A) :
    (0 < μ ∧ μ % (2 * A) = A % (2 * A)) ↔ ∃ j, μ = mex_odd_candidate A j := by
  have hlt : A < 2 * A := by
    calc
      A = A * 1 := by simp
      _ < A * 2 := (Nat.mul_lt_mul_left hA).2 (by omega)
      _ = 2 * A := by ac_rfl
  constructor
  · rintro ⟨_hμ, hmod⟩
    have hmodA : μ % (2 * A) = A := hmod.trans (Nat.mod_eq_of_lt hlt)
    have hdecomp := Nat.div_add_mod μ (2 * A)
    rw [hmodA] at hdecomp
    let q := μ / (2 * A)
    refine ⟨q, ?_⟩
    calc
      μ = 2 * A * q + A := by simpa only [q] using hdecomp.symm
      _ = mex_odd_candidate A q := by simp only [mex_odd_candidate]; ring
  · rintro ⟨j, rfl⟩
    refine ⟨mex_odd_candidate_pos A hA j, ?_⟩
    calc
      mex_odd_candidate A j % (2 * A) = A * ((2 * j + 1) % 2) := by
        rw [mex_odd_candidate, mul_comm 2 A]
        exact Nat.mul_mod_mul_left A (2 * j + 1) 2
      _ = A := by
        have hodd : (2 * j + 1) % 2 = 1 := by omega
        rw [hodd, mul_one]
      _ = A % (2 * A) := (Nat.mod_eq_of_lt hlt).symm

private theorem mex_odd_selected_iff (A j : ℕ) (hA : 0 < A) :
    mex_odd_candidate A j % (2 * (2 * A)) = A % (2 * (2 * A)) ↔ Even j := by
  have hdenom : 2 * (2 * A) = A * 4 := by ring
  have hlt : A < 2 * (2 * A) := by
    rw [hdenom]
    calc
      A = A * 1 := by simp
      _ < A * 4 := (Nat.mul_lt_mul_left hA).2 (by omega)
  have hleft : mex_odd_candidate A j % (2 * (2 * A)) = A * ((2 * j + 1) % 4) := by
    rw [mex_odd_candidate, hdenom]
    exact Nat.mul_mod_mul_left A (2 * j + 1) 4
  rw [hleft, Nat.mod_eq_of_lt hlt]
  have hcancel : A * ((2 * j + 1) % 4) = A ↔ (2 * j + 1) % 4 = 1 := by
    simpa only [mul_one] using
      (Nat.mul_left_cancel_iff hA (m := (2 * j + 1) % 4) (k := 1))
  rw [hcancel, Nat.even_iff]
  omega

private theorem mex_linear_target_iff {N A : ℕ} (hA : 0 < A) (p : Nat.Partition N) :
    (∃ μ, 0 < μ ∧ μ % A = A % A ∧ μ ∉ p.parts ∧
      (∀ k, 0 < k → k < μ → k % A = A % A → k ∈ p.parts) ∧
      μ % (2 * A) = A % (2 * A)) ↔
      Even (mex_index (mex_linear_candidate A) (mex_linear_candidate_strict A hA) p) := by
  exact mex_target_iff_even_index (mex_linear_candidate A)
    (mex_linear_candidate_strict A hA)
    (fun x => x % A = A % A) (fun x => x % (2 * A) = A % (2 * A))
    (fun x => mex_linear_candidate_iff A x hA)
    (fun j => mex_linear_selected_iff A j hA) p

private theorem mex_odd_target_iff {N A : ℕ} (hA : 0 < A) (p : Nat.Partition N) :
    (∃ μ, 0 < μ ∧ μ % (2 * A) = A % (2 * A) ∧ μ ∉ p.parts ∧
      (∀ k, 0 < k → k < μ → k % (2 * A) = A % (2 * A) → k ∈ p.parts) ∧
      μ % (2 * (2 * A)) = A % (2 * (2 * A))) ↔
      Even (mex_index (mex_odd_candidate A) (mex_odd_candidate_strict A hA) p) := by
  exact mex_target_iff_even_index (mex_odd_candidate A)
    (mex_odd_candidate_strict A hA)
    (fun x => x % (2 * A) = A % (2 * A))
    (fun x => x % (2 * (2 * A)) = A % (2 * (2 * A)))
    (fun x => mex_odd_candidate_iff A x hA)
    (fun j => mex_odd_selected_iff A j hA) p

/-- **Lifting partition congruences to mex partition functions.** For a partition $\lambda$, a
positive integer $A$ and a natural number $c$, let $\operatorname{mex}_{A,c}(\lambda)$ be the
smallest positive integer congruent to $c$ modulo $A$ that is not a part of $\lambda$, and let
$p_{A,c}(N)$ be the number of partitions $\lambda$ of $N$ with
$\operatorname{mex}_{A,c}(\lambda) \equiv c \pmod{2A}$. Let $p(N)$ be the number of partitions of
$N$. Let $m$, $a$ and $b$ be natural numbers with $m \ge 1$ and $b < a$, and suppose that $m$
divides $p(an + b)$ for every natural number $n$. Then for every integer $t \ge 1$ and every
natural number $n$, $m$ divides both $p_{at,at}(an + b)$ and $p_{2at,at}(an + b)$.

Because $b < a$, the hypothesis covers the whole residue class of $b$ modulo $a$; for $b \ge a$
the lift would need $p$ at arguments below $b$, which the hypothesis does not cover.

The proof follows the Andrews–Newman mex decomposition used by Barman and Singh: remove one copy
of every forced earlier mex candidate. The exact-mex fibers then telescope, while every removed
prefix sum remains a multiple of $a$.

Proves `Wanted` entry `mesh_partition_congruence_lift`.

Source: Rupam Barman and Ajit Singh, "Mex-Related Partition Functions of
Andrews and Newman," Journal of Integer Sequences 24 (2021),
Article 21.6.3, Theorem (label thm2), lines 172–182,
https://cs.uwaterloo.ca/journals/JIS/VOL24/Barman/barman3.tex
-/
public theorem mesh_partition_congruence_lift
    (m a b : ℕ) (_hm : 0 < m) (ha : 0 < a) (hb : b < a)
    (hbase : ∀ n : ℕ, m ∣ Fintype.card (Nat.Partition (a * n + b))) :
    ∀ t : ℕ, 0 < t →
      (∀ n : ℕ, m ∣ (@Finset.filter (Nat.Partition (a * n + b))
        (fun lam => ∃ μ : ℕ, 0 < μ ∧ μ % (a * t) = (a * t) % (a * t) ∧
          μ ∉ lam.parts ∧
          (∀ k : ℕ, 0 < k → k < μ → k % (a * t) = (a * t) % (a * t) →
            k ∈ lam.parts) ∧
          μ % (2 * (a * t)) = (a * t) % (2 * (a * t)))
        (Classical.decPred _) Finset.univ).card) ∧
      (∀ n : ℕ, m ∣ (@Finset.filter (Nat.Partition (a * n + b))
        (fun lam => ∃ μ : ℕ, 0 < μ ∧ μ % (2 * a * t) = (a * t) % (2 * a * t) ∧
          μ ∉ lam.parts ∧
          (∀ k : ℕ, 0 < k → k < μ → k % (2 * a * t) = (a * t) % (2 * a * t) →
            k ∈ lam.parts) ∧
          μ % (2 * (2 * a * t)) = (a * t) % (2 * (2 * a * t)))
        (Classical.decPred _) Finset.univ).card) := by
  classical
  intro t ht
  have hA : 0 < a * t := Nat.mul_pos ha ht
  constructor
  · intro n
    have hc := mex_linear_candidate_strict (a * t) hA
    have hcpos := mex_linear_candidate_pos (a * t) hA
    have hsum : ∀ j,
        (mex_prefix (mex_linear_candidate (a * t)) j).sum =
          a * (t * ∑ i ∈ Finset.range j, (i + 1)) := by
      intro j
      change (mex_prefix (fun i => (a * t) * (i + 1)) j).sum = _
      exact mex_scaled_prefix_sum a t (fun i => i + 1)
        (by
          intro i k hik
          apply Nat.mul_lt_mul_of_pos_left _ hA
          omega) j
    have hdiv := mex_even_index_card_dvd m a b n hb hbase
      (mex_linear_candidate (a * t)) hc hcpos
      (fun j => t * ∑ i ∈ Finset.range j, (i + 1)) hsum
    have hfilter :
        (@Finset.filter (Nat.Partition (a * n + b))
          (fun lam => ∃ μ : ℕ, 0 < μ ∧ μ % (a * t) = (a * t) % (a * t) ∧
            μ ∉ lam.parts ∧
            (∀ k : ℕ, 0 < k → k < μ → k % (a * t) = (a * t) % (a * t) →
              k ∈ lam.parts) ∧
            μ % (2 * (a * t)) = (a * t) % (2 * (a * t)))
          (Classical.decPred _) Finset.univ) =
          (Finset.univ.filter fun p : Nat.Partition (a * n + b) =>
            Even (mex_index (mex_linear_candidate (a * t)) hc p)) := by
      apply Finset.filter_congr
      intro p hp
      exact mex_linear_target_iff hA p
    rw [hfilter]
    exact hdiv
  · intro n
    have hc := mex_odd_candidate_strict (a * t) hA
    have hcpos := mex_odd_candidate_pos (a * t) hA
    have hsum : ∀ j,
        (mex_prefix (mex_odd_candidate (a * t)) j).sum =
          a * (t * ∑ i ∈ Finset.range j, (2 * i + 1)) := by
      intro j
      change (mex_prefix (fun i => (a * t) * (2 * i + 1)) j).sum = _
      exact mex_scaled_prefix_sum a t (fun i => 2 * i + 1)
        (by
          intro i k hik
          apply Nat.mul_lt_mul_of_pos_left _ hA
          omega) j
    have hdiv := mex_even_index_card_dvd m a b n hb hbase
      (mex_odd_candidate (a * t)) hc hcpos
      (fun j => t * ∑ i ∈ Finset.range j, (2 * i + 1)) hsum
    have hfilter :
        (@Finset.filter (Nat.Partition (a * n + b))
          (fun lam => ∃ μ : ℕ, 0 < μ ∧ μ % (2 * a * t) = (a * t) % (2 * a * t) ∧
            μ ∉ lam.parts ∧
            (∀ k : ℕ, 0 < k → k < μ → k % (2 * a * t) = (a * t) % (2 * a * t) →
              k ∈ lam.parts) ∧
            μ % (2 * (2 * a * t)) = (a * t) % (2 * (2 * a * t)))
          (Classical.decPred _) Finset.univ) =
          (Finset.univ.filter fun p : Nat.Partition (a * n + b) =>
            Even (mex_index (mex_odd_candidate (a * t)) hc p)) := by
      apply Finset.filter_congr
      intro p hp
      simpa only [mul_assoc] using mex_odd_target_iff hA p
    rw [hfilter]
    exact hdiv

end MetaMathlibExt
