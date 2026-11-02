/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import MathlibExt.NumberTheory.Padics.CasselsEmbedding
import MathlibExt.NumberTheory.Padics.Strassmann

import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

open scoped BigOperators Matrix

namespace MetaMathlibExt

/-- From per-residue-class information, assemble the finite set and the
finite set of progressions. -/
private theorem sml_assemble {K : Type*} [Zero K] (u : ℕ → K) (N : ℕ) (hN : 0 < N)
    (h : ∀ a < N, (∀ t, u (a + N * t) = 0) ∨ (Set.Finite {t | u (a + N * t) = 0})) :
    ∃ (F : Finset ℕ) (P : Finset (ℕ × ℕ)), (∀ p ∈ P, 0 < p.2) ∧
      {n | u n = 0} = ↑F ∪ ⋃ p ∈ (↑P : Set (ℕ × ℕ)),
        {n | ∃ t, n = p.1 + p.2 * t} := by
  classical
  let P : Finset (ℕ × ℕ) :=
    ((Finset.range N).filter (fun a => ∀ t, u (a + N * t) = 0)).image (fun a => (a, N))
  let G : Finset ℕ := (Finset.range N).filter (fun a => ¬ ∀ t, u (a + N * t) = 0)
  have hfin : ∀ a ∈ G, Set.Finite {t | u (a + N * t) = 0} := by
    intro a ha
    have haN : a < N := Finset.mem_range.mp (Finset.mem_of_mem_filter _ ha)
    exact ((h a haN).resolve_left (Finset.mem_filter.mp ha |>.2))
  refine ⟨G.biUnion (fun a =>
    if ha : a ∈ G then ((hfin a ha).toFinset).image (fun t => a + N * t) else ∅),
    P, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    exact hN
  · ext n
    have hdecomp : n = n % N + N * (n / N) := (Nat.mod_add_div n N).symm
    simp only [Set.mem_union, Finset.mem_coe, Finset.mem_biUnion, Set.mem_iUnion]
    constructor
    · intro hn
      have haN : n % N < N := Nat.mod_lt _ hN
      by_cases hall : ∀ t, u (n % N + N * t) = 0
      · right
        refine ⟨(n % N, N), ?_, n / N, hdecomp⟩
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr
          ⟨n % N, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr haN, hall⟩, rfl⟩)
      · left
        have haG : n % N ∈ G :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr haN, hall⟩
        refine ⟨n % N, haG, ?_⟩
        rw [dite_eq_left haG]
        have hzero : u (n % N + N * (n / N)) = 0 := by rw [← hdecomp]; exact hn
        exact Finset.mem_image.mpr
          ⟨n / N, (Set.Finite.mem_toFinset (hfin (n % N) haG)).mpr hzero,
            hdecomp.symm⟩
    · rintro (⟨a, haG, hmem⟩ | ⟨p, hpP, t, ht⟩)
      · rw [dite_eq_left haG] at hmem
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hmem
        rw [Set.Finite.mem_toFinset] at ht
        exact ht
      · obtain ⟨a, haP, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hpP)
        have : n = a + N * t := ht
        rw [this]
        exact (Finset.mem_filter.mp haP |>.2) t

/-- Shifting the sequence by one preserves the conclusion. -/
private theorem sml_shift {K : Type*} [Zero K] (u : ℕ → K)
    (h : ∃ (F : Finset ℕ) (P : Finset (ℕ × ℕ)), (∀ p ∈ P, 0 < p.2) ∧
      {n | u (n + 1) = 0} = ↑F ∪ ⋃ p ∈ (↑P : Set (ℕ × ℕ)),
        {n | ∃ t, n = p.1 + p.2 * t}) :
    ∃ (F : Finset ℕ) (P : Finset (ℕ × ℕ)), (∀ p ∈ P, 0 < p.2) ∧
      {n | u n = 0} = ↑F ∪ ⋃ p ∈ (↑P : Set (ℕ × ℕ)),
        {n | ∃ t, n = p.1 + p.2 * t} := by
  obtain ⟨F', P', hpos, heq⟩ := h
  have fwd : ∀ n' : ℕ, u (n' + 1) = 0 →
      (n' ∈ F') ∨ ∃ p, p ∈ (↑P' : Set (ℕ × ℕ)) ∧ ∃ t, n' = p.1 + p.2 * t := by
    intro n' hn'
    have hmem : n' ∈ (↑F' : Set ℕ) ∪ ⋃ q ∈ (↑P' : Set (ℕ × ℕ)),
        {n | ∃ s, n = q.1 + q.2 * s} := by
      rw [← heq]
      exact hn'
    rcases hmem with hF | hU
    · exact Or.inl (Finset.mem_coe.mp hF)
    · obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hU
      obtain ⟨hpP, t, ht⟩ := Set.mem_iUnion.mp hp
      exact Or.inr ⟨p, hpP, t, ht⟩
  have bwdF : ∀ m : ℕ, m ∈ F' → u (m + 1) = 0 := by
    intro m hm
    have hmem : m ∈ (↑F' : Set ℕ) ∪ ⋃ q ∈ (↑P' : Set (ℕ × ℕ)),
        {n | ∃ s, n = q.1 + q.2 * s} := Or.inl (Finset.mem_coe.mpr hm)
    rw [← heq] at hmem
    exact hmem
  have bwdP : ∀ (p : ℕ × ℕ) (t : ℕ), p ∈ (↑P' : Set (ℕ × ℕ)) →
      u ((p.1 + 1) + p.2 * t) = 0 := by
    intro p t hpP
    have hmem : p.1 + p.2 * t ∈ (↑F' : Set ℕ) ∪ ⋃ q ∈ (↑P' : Set (ℕ × ℕ)),
        {n | ∃ s, n = q.1 + q.2 * s} :=
      Set.mem_union_right _ (Set.mem_biUnion hpP ⟨t, rfl⟩)
    rw [← heq] at hmem
    have h0' : u ((p.1 + p.2 * t) + 1) = 0 := hmem
    have : (p.1 + 1) + p.2 * t = (p.1 + p.2 * t) + 1 := by omega
    rwa [this]
  by_cases h0 : u 0 = 0
  · refine ⟨F'.image (· + 1) ∪ {0}, P'.image (fun p => (p.1 + 1, p.2)), ?_, ?_⟩
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact hpos q hq
    · ext n
      simp only [Set.mem_union, Finset.mem_coe, Finset.mem_union,
        Finset.mem_image, Finset.mem_singleton, Set.mem_iUnion]
      constructor
      · intro hn
        by_cases hz : n = 0
        · subst hz
          exact Or.inl (Or.inr rfl)
        · obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
          rcases fwd n' hn with hm | ⟨p, hpP, t, ht⟩
          · exact Or.inl (Or.inl ⟨n', hm, rfl⟩)
          · refine Or.inr ⟨(p.1 + 1, p.2),
              ⟨p, Finset.mem_coe.mp hpP, rfl⟩, t, ?_⟩
            change n' + 1 = (p.1 + 1) + p.2 * t
            omega
      · intro hmem
        rcases hmem with hF | hU
        · rcases hF with ⟨m, hm, rfl⟩ | rfl
          · exact bwdF m hm
          · exact h0
        · obtain ⟨p, hpP, t, ht⟩ := hU
          obtain ⟨q, hq, rfl⟩ := hpP
          rw [show n = (q.1 + 1) + q.2 * t from ht]
          exact bwdP q t (Finset.mem_coe.mp hq)
  · refine ⟨F'.image (· + 1), P'.image (fun p => (p.1 + 1, p.2)), ?_, ?_⟩
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact hpos q hq
    · ext n
      simp only [Set.mem_union, Finset.mem_coe, Finset.mem_image, Set.mem_iUnion]
      constructor
      · intro hn
        by_cases hz : n = 0
        · subst hz
          exact absurd hn h0
        · obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
          rcases fwd n' hn with hm | ⟨p, hpP, t, ht⟩
          · exact Or.inl ⟨n', hm, rfl⟩
          · refine Or.inr ⟨(p.1 + 1, p.2),
              ⟨p, Finset.mem_coe.mp hpP, rfl⟩, t, ?_⟩
            change n' + 1 = (p.1 + 1) + p.2 * t
            omega
      · intro hmem
        rcases hmem with hF | hU
        · obtain ⟨m, hm, rfl⟩ := hF
          exact bwdF m hm
        · obtain ⟨p, hpP, t, ht⟩ := hU
          obtain ⟨q, hq, rfl⟩ := hpP
          rw [show n = (q.1 + 1) + q.2 * t from ht]
          exact bwdP q t (Finset.mem_coe.mp hq)

/-- Every term of the recurrence lies in a subring containing the data. -/
private theorem sml_closure_mem {K : Type*} [Field K] (k : ℕ) (c u : ℕ → K)
    (R : Subring K) (hc : ∀ i < k, c i ∈ R) (hu : ∀ i < k, u i ∈ R)
    (hrec : ∀ n, u (n + k) = ∑ i ∈ Finset.range k, c i * u (n + i)) :
    ∀ n, u n ∈ R := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < k
    · exact hu n hn
    · have hnn : u n = u ((n - k) + k) := by congr 1; omega
      rw [hnn, hrec]
      apply R.sum_mem
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      apply mul_mem (hc i hik)
      apply ih
      omega

/-- Companion matrix of the recurrence, invertible mod `p`. -/
private theorem sml_companion (p : ℕ) [Fact p.Prime] (m : ℕ)
    (x γ : ℕ → ℤ_[p]) (hγ : IsUnit (γ 0))
    (hrec : ∀ n, x (n + (m + 1)) = ∑ i ∈ Finset.range (m + 1), γ i * x (n + i)) :
    ∃ A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[p],
      (∀ n, (fun i : Fin (m + 1) => x (n + 1 + i.val)) = A *ᵥ (fun i => x (n + i.val)))
      ∧ IsUnit (PadicInt.toZMod.mapMatrix A) := by
  classical
  set A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[p] :=
    fun i j => if j.val = i.val + 1 then 1 else if i.val = m then γ j.val else 0 with hA
  have hrow : ∀ (n : ℕ) (i : Fin (m + 1)),
      (A *ᵥ (fun j : Fin (m + 1) => x (n + j.val))) i = x (n + 1 + i.val) := by
    intro n i
    rw [Matrix.mulVec_apply_eq_sum]
    by_cases hi : i.val < m
    · have hib : i.val + 1 < m + 1 := by omega
      have hcond : ((⟨i.val + 1, hib⟩ : Fin (m + 1)).val) = i.val + 1 := rfl
      have hvan : ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))),
          j ≠ ⟨i.val + 1, hib⟩ → A i j * x (n + j.val) = 0 := by
        intro j _ hne
        have hj : ¬ j.val = i.val + 1 := fun h => hne (Fin.ext (h.trans hcond.symm))
        rw [hA]
        simp only [hj, ite_false]
        have him : ¬ i.val = m := by omega
        simp only [him, ite_false, zero_mul]
      have hval : A i ⟨i.val + 1, hib⟩ * x (n + (⟨i.val + 1, hib⟩ : Fin (m + 1)).val)
          = x (n + 1 + i.val) := by
        rw [hA]
        simp only [ite_true, one_mul]
        congr 1
        omega
      calc ∑ j : Fin (m + 1), A i j * x (n + j.val)
          = A i ⟨i.val + 1, hib⟩ * x (n + (⟨i.val + 1, hib⟩ : Fin (m + 1)).val) :=
            Finset.sum_eq_single _ hvan
              (fun hcon => absurd (Finset.mem_univ _) hcon)
        _ = x (n + 1 + i.val) := hval
    · have hiLt := i.isLt
      have him : i.val = m := by omega
      have hAg : ∀ j : Fin (m + 1),
          A i j * x (n + j.val) = γ j.val * x (n + j.val) := by
        intro j
        have hjlt := j.isLt
        have hj : ¬ j.val = i.val + 1 := by omega
        rw [hA]
        simp only [hj, ite_false]
        simp only [him, ite_true]
      calc ∑ j : Fin (m + 1), A i j * x (n + j.val)
          = ∑ j : Fin (m + 1), γ j.val * x (n + j.val) :=
            Finset.sum_congr rfl (fun j _ => hAg j)
        _ = ∑ k ∈ Finset.range (m + 1), γ k * x (n + k) :=
            Fin.sum_univ_eq_sum_range (fun k => γ k * x (n + k)) (m + 1)
        _ = x (n + (m + 1)) := (hrec n).symm
        _ = x (n + 1 + i.val) := by congr 1; omega
  have hγbar : IsUnit (PadicInt.toZMod (γ 0)) := hγ.map _
  have hγne : PadicInt.toZMod (γ 0) ≠ 0 := hγbar.ne_zero
  have hred : ∀ i j : Fin (m + 1),
      PadicInt.toZMod.mapMatrix A i j =
        if j.val = i.val + 1 then 1
        else if i.val = m then PadicInt.toZMod (γ j.val) else 0 := by
    intro i j
    have h0 : PadicInt.toZMod.mapMatrix A i j = PadicInt.toZMod (A i j) := rfl
    rw [h0, hA]
    by_cases hj : j.val = i.val + 1
    · simp only [ite_eq_left hj, map_one]
    · simp only [ite_eq_right hj]
      by_cases hm2 : i.val = m
      · simp only [ite_eq_left hm2]
      · simp only [ite_eq_right hm2, map_zero]
  have hker : ∀ z : Fin (m + 1) → ZMod p,
      PadicInt.toZMod.mapMatrix A *ᵥ z = 0 → z = 0 := by
    intro z hz
    have hentry : ∀ i : Fin (m + 1),
        (PadicInt.toZMod.mapMatrix A *ᵥ z) i = 0 := fun i => by rw [hz]; rfl
    have hshift : ∀ j : Fin (m + 1), j.val ≠ 0 → z j = 0 := by
      intro j hj0
      have hjlt := j.isLt
      have hib : j.val - 1 + 1 < m + 1 := by omega
      have hival : ((⟨j.val - 1, by omega⟩ : Fin (m + 1)).val) = j.val - 1 := rfl
      have himlt : (⟨j.val - 1, by omega⟩ : Fin (m + 1)).val < m := by omega
      have himne : ¬ (⟨j.val - 1, by omega⟩ : Fin (m + 1)).val = m := by omega
      have hcond : ((⟨(⟨j.val - 1, by omega⟩ : Fin (m + 1)).val + 1, hib⟩ :
        Fin (m + 1)).val) = (⟨j.val - 1, by omega⟩ : Fin (m + 1)).val + 1 := rfl
      have hji : (⟨(⟨j.val - 1, by omega⟩ : Fin (m + 1)).val + 1, hib⟩ :
          Fin (m + 1)) = j := by
        apply Fin.ext
        rw [hcond, hival]
        omega
      have hsum : ∑ k : Fin (m + 1),
          PadicInt.toZMod.mapMatrix A ⟨j.val - 1, by omega⟩ k * z k = z j := by
        have hvan : ∀ k ∈ (Finset.univ : Finset (Fin (m + 1))),
            k ≠ ⟨(⟨j.val - 1, by omega⟩ : Fin (m + 1)).val + 1, hib⟩ →
            PadicInt.toZMod.mapMatrix A ⟨j.val - 1, by omega⟩ k * z k = 0 := by
          intro k _ hne
          have hk : ¬ k.val = (⟨j.val - 1, by omega⟩ : Fin (m + 1)).val + 1 :=
            fun h => hne (Fin.ext (h.trans hcond.symm))
          rw [hred, ite_eq_right hk, ite_eq_right himne, zero_mul]
        have hval : PadicInt.toZMod.mapMatrix A ⟨j.val - 1, by omega⟩
              ⟨(⟨j.val - 1, by omega⟩ : Fin (m + 1)).val + 1, hib⟩
              * z ⟨(⟨j.val - 1, by omega⟩ : Fin (m + 1)).val + 1, hib⟩
            = z j := by
          rw [hred, ite_eq_left hcond, one_mul, hji]
        calc ∑ k : Fin (m + 1),
              PadicInt.toZMod.mapMatrix A ⟨j.val - 1, by omega⟩ k * z k
            = PadicInt.toZMod.mapMatrix A ⟨j.val - 1, by omega⟩
              ⟨(⟨j.val - 1, by omega⟩ : Fin (m + 1)).val + 1, hib⟩
              * z ⟨(⟨j.val - 1, by omega⟩ : Fin (m + 1)).val + 1, hib⟩ :=
              Finset.sum_eq_single _ hvan
                (fun hcon => absurd (Finset.mem_univ _) hcon)
          _ = z j := hval
      have h2 := hentry ⟨j.val - 1, by omega⟩
      rw [Matrix.mulVec_apply_eq_sum, hsum] at h2
      exact h2
    have hlast : z ⟨0, Nat.zero_lt_succ m⟩ = 0 := by
      have e0 : ((⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)).val) = 0 := rfl
      have em : ((⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)).val) = m := rfl
      have hvan : ∀ k ∈ (Finset.univ : Finset (Fin (m + 1))),
          k ≠ ⟨0, Nat.zero_lt_succ m⟩ →
          PadicInt.toZMod.mapMatrix A ⟨m, Nat.lt_succ_self m⟩ k * z k = 0 := by
        intro k _ hne
        have hkv : k.val ≠ 0 := by
          intro h
          apply hne
          apply Fin.ext
          rw [e0]
          exact h
        rw [hshift k hkv, mul_zero]
      have hval : PadicInt.toZMod.mapMatrix A ⟨m, Nat.lt_succ_self m⟩
            ⟨0, Nat.zero_lt_succ m⟩ * z ⟨0, Nat.zero_lt_succ m⟩
          = PadicInt.toZMod (γ 0) * z ⟨0, Nat.zero_lt_succ m⟩ := by
        have hk : ¬ ((⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)).val
            = (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)).val + 1) := by
          rw [e0, em]
          omega
        rw [hred, ite_eq_right hk, ite_eq_left em]
      have hsum : ∑ k : Fin (m + 1),
          PadicInt.toZMod.mapMatrix A ⟨m, Nat.lt_succ_self m⟩ k * z k
          = PadicInt.toZMod (γ 0) * z ⟨0, Nat.zero_lt_succ m⟩ :=
        (Finset.sum_eq_single _ hvan
          (fun hcon => absurd (Finset.mem_univ _) hcon)).trans hval
      have h0 := hentry ⟨m, Nat.lt_succ_self m⟩
      rw [Matrix.mulVec_apply_eq_sum, hsum] at h0
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hγne
      · exact h
    funext j
    by_cases hj0 : j.val = 0
    · have hjj : j = ⟨0, Nat.zero_lt_succ m⟩ := Fin.ext hj0
      rw [hjj]
      exact hlast
    · exact hshift j hj0
  refine ⟨A, fun n => funext fun i => (hrow n i).symm, ?_⟩
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  have hsub : PadicInt.toZMod.mapMatrix A *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, sub_eq_zero.mpr hvw]
  have hkerw := hker (v - w) hsub
  exact sub_eq_zero.mp hkerw

/-- A power of the companion matrix is `1` modulo `p`. -/
private theorem sml_period (p : ℕ) [Fact p.Prime] (m : ℕ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[p])
    (hA : IsUnit (PadicInt.toZMod.mapMatrix A)) :
    ∃ N : ℕ, 0 < N ∧ ∃ B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[p],
      A ^ N = 1 + (p : ℤ_[p]) • B := by
  classical
  obtain ⟨u, hu⟩ := hA
  have hNpos : 0 < orderOf u := orderOf_pos u
  have hpow : u ^ orderOf u = 1 := pow_orderOf_eq_one u
  have hred : PadicInt.toZMod.mapMatrix (A ^ orderOf u) = 1 := by
    rw [map_pow, ← hu, ← Units.val_pow_eq_pow_val, hpow, Units.val_one]
  have hmem : ∀ i j : Fin (m + 1),
      PadicInt.toZMod ((A ^ orderOf u - 1) i j) = 0 := by
    intro i j
    have e : PadicInt.toZMod.mapMatrix (A ^ orderOf u - 1)
        = PadicInt.toZMod.mapMatrix (A ^ orderOf u) - 1 := by
      rw [map_sub, map_one]
    have h0 : PadicInt.toZMod ((A ^ orderOf u - 1) i j)
        = (PadicInt.toZMod.mapMatrix (A ^ orderOf u) - 1) i j := by
      rw [← e]
      rfl
    rw [h0, hred]
    simp
  have hdiv : ∀ i j : Fin (m + 1), (p : ℤ_[p]) ∣ (A ^ orderOf u - 1) i j := by
    intro i j
    have hker : (A ^ orderOf u - 1) i j ∈ RingHom.ker PadicInt.toZMod :=
      RingHom.mem_ker.mpr (hmem i j)
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton] at hker
    exact hker
  choose B hB using hdiv
  have hex : ∃ B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[p], ∀ i j,
      (A ^ orderOf u - 1) i j = (p : ℤ_[p]) * B i j := ⟨B, hB⟩
  obtain ⟨B, hB⟩ := hex
  refine ⟨orderOf u, hNpos, B, ?_⟩
  funext i j
  have h1 : ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[p]) + (p : ℤ_[p]) • B) i j
      = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[p]) i j + (p : ℤ_[p]) * B i j := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [h1, ← hB i j,
    add_comm ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[p]) i j)]
  exact (sub_add_cancel _ _).symm

/-- The per-term binomial identity. -/
private theorem sml_binomial (p : ℕ) [Fact p.Prime] (m N : ℕ)
    (s : ℕ → Fin (m + 1) → ℤ_[p]) (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[p])
    (hs : ∀ n, s (n + 1) = A *ᵥ s n)
    (hAB : A ^ N = 1 + (p : ℤ_[p]) • B) (a t : ℕ) :
    s (a + N * t) = ∑ j ∈ Finset.range (t + 1),
      ((t.choose j : ℤ_[p]) • ((((p : ℤ_[p]) ^ j) • ((B ^ j) *ᵥ s a)))) := by
  classical
  have hsn : ∀ (k n : ℕ), s (n + k) = (A ^ k) *ᵥ s n := by
    intro k
    induction k with
    | zero =>
      intro n
      simp only [add_zero, pow_zero, Matrix.one_mulVec]
    | succ k ih =>
      intro n
      have e1 : n + (k + 1) = (n + k) + 1 := by omega
      rw [e1, hs (n + k), ih n, Matrix.mulVec_mulVec, ← pow_succ']
  have hnat : ∀ (n : ℕ) (v : Fin (m + 1) → ℤ_[p]),
      (↑n : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[p]) *ᵥ v
        = (↑n : ℤ_[p]) • v := by
    intro n v
    have hcast : (↑n : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[p])
        = n • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[p]) := by
      rw [nsmul_eq_mul, mul_one]
    rw [hcast, Matrix.smul_mulVec, Matrix.one_mulVec, nsmul_eq_mul]
    funext i
    exact (smul_eq_mul _ _).symm
  have hbase : s (a + N * t) = (A ^ (N * t)) *ᵥ s a := hsn (N * t) a
  have hcomm : ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[p]) + (p : ℤ_[p]) • B)
      = ((p : ℤ_[p]) • B) + 1 := add_comm _ _
  rw [pow_mul, hAB, hcomm, (Commute.one_right _).add_pow t,
    Matrix.sum_mulVec] at hbase
  refine hbase.trans ?_
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [one_pow, mul_one, smul_pow, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
    hnat, Matrix.mulVec_smul]
  exact smul_comm _ _ _

/-- The key norm estimate `‖p ^ j / j!‖ ^ 2 ≤ (p⁻¹) ^ j` for `p ≥ 3`. -/
private theorem sml_pow_div_factorial_norm (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (j : ℕ) :
    ‖(p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])‖ ^ 2
      ≤ ((p : ℝ)⁻¹) ^ j := by
  have hfact : ((Nat.factorial j : ℕ) : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have h1 : ‖(p : ℚ_[p]) ^ j‖ = (p : ℝ) ^ (-(j : ℤ)) := Padic.norm_p_pow j
  have h2 : ‖((Nat.factorial j : ℕ) : ℚ_[p])‖
      = (p : ℝ) ^ (-((padicValNat p (Nat.factorial j) : ℕ) : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hfact, Padic.valuation_natCast]
  have hleg : (p - 1) * padicValNat p (Nat.factorial j) = j - (Nat.digits p j).sum :=
    sub_one_mul_padicValNat_factorial j
  have h2v : 2 * padicValNat p (Nat.factorial j) ≤ j := by
    have h1' : 2 ≤ p - 1 := by omega
    have h2' : 2 * padicValNat p (Nat.factorial j) ≤ (p - 1) * padicValNat p (Nat.factorial j) :=
      mul_le_mul_of_nonneg_right h1' (Nat.zero_le _)
    have h3' : (p - 1) * padicValNat p (Nat.factorial j) ≤ j := by
      rw [hleg]
      exact Nat.sub_le _ _
    omega
  have hP1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hP0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  rw [norm_div, h1, h2, ← zpow_sub₀ hP0, pow_two, ← zpow_add₀ hP0,
    inv_pow, ← zpow_natCast, ← zpow_neg]
  apply zpow_le_zpow_right₀ hP1
  have h2vZ : 2 * ((padicValNat p (Nat.factorial j) : ℕ) : ℤ) ≤ (j : ℤ) := by
    exact_mod_cast h2v
  omega

/-- The p-adic power series attached to a residue class. -/
private theorem sml_series (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (w : ℕ → ℚ_[p]) (hw : ∀ j, ‖w j‖ ≤ 1) :
    ∃ b : ℕ → ℚ_[p],
      Filter.Tendsto b Filter.cofinite (nhds 0)
      ∧ ∀ t : ℕ, ∑' m, b m * (t : ℚ_[p]) ^ m
          = ∑ j ∈ Finset.range (t + 1),
            (t.choose j : ℚ_[p]) * (p : ℚ_[p]) ^ j * w j := by
  classical
  have hpr : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 0 ≤ p)
  have hpinv : (0 : ℝ) ≤ ((p : ℝ))⁻¹ := inv_nonneg.mpr hpr
  have hp1 : ((p : ℝ))⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < p))
  have hp1le : ((p : ℝ))⁻¹ ≤ 1 := le_of_lt hp1
  have hfact : ∀ j : ℕ, ((Nat.factorial j : ℕ) : ℚ_[p]) ≠ 0 :=
    fun j => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  set e : ℕ → ℕ → ℚ_[p] := fun j m =>
    ((p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])) * w j
      * (((descPochhammer ℤ j).coeff m : ℤ) : ℚ_[p])
  have heq : ∀ j m : ℕ, e j m
      = ((p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])) * w j
        * (((descPochhammer ℤ j).coeff m : ℤ) : ℚ_[p]) := fun j m => rfl
  have hcoeff : ∀ j m : ℕ,
      ‖((((descPochhammer ℤ j).coeff m : ℤ)) : ℚ_[p])‖ ≤ 1 :=
    fun j m => Padic.norm_int_le_one _
  have hvan : ∀ j m : ℕ, j < m → e j m = 0 := by
    intro j m hjm
    rw [heq j m]
    have hc : (descPochhammer ℤ j).coeff m = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [descPochhammer_natDegree]
      exact hjm
    rw [hc, Int.cast_zero, mul_zero]
  have hbound : ∀ j m : ℕ,
      ‖e j m‖ ≤ ‖(p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])‖ := by
    intro j m
    rw [heq j m, norm_mul, norm_mul]
    have h1 : ‖(p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])‖ * ‖w j‖
        ≤ ‖(p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])‖ * 1 :=
      mul_le_mul_of_nonneg_left (hw j) (norm_nonneg _)
    calc ‖(p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])‖ * ‖w j‖
            * ‖((((descPochhammer ℤ j).coeff m : ℤ)) : ℚ_[p])‖
        ≤ (‖(p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])‖ * 1) * 1 :=
          mul_le_mul h1 (hcoeff j m) (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) zero_le_one)
      _ = ‖(p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])‖ := by ring
  have hu0 : Filter.Tendsto
      (fun j => ‖(p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])‖)
      Filter.cofinite (nhds 0) := by
    have hsq0 : Filter.Tendsto
        (fun j => ‖(p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])‖ ^ 2)
        Filter.cofinite (nhds 0) := by
      apply squeeze_zero (fun j => pow_nonneg (norm_nonneg _) 2)
        (fun j => sml_pow_div_factorial_norm p hp j)
      rw [Nat.cofinite_eq_atTop]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one hpinv hp1
    have h : Filter.Tendsto (fun j => Real.sqrt (‖(p : ℚ_[p]) ^ j
        / ((Nat.factorial j : ℕ) : ℚ_[p])‖ ^ 2))
        Filter.cofinite (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hsq0
    rw [Real.sqrt_zero] at h
    exact Filter.Tendsto.congr (fun j => Real.sqrt_sq (norm_nonneg _)) h
  have hsum : ∀ m : ℕ, Summable (fun j => e j m) := by
    intro m
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    exact squeeze_zero_norm (fun j => hbound j m) hu0
  have hsq : ∀ m : ℕ, ‖∑' j, e j m‖ ^ 2 ≤ ((p : ℝ))⁻¹ ^ m := by
    intro m
    have hle : ∀ j : ℕ, ‖e j m‖ ≤ Real.sqrt (((p : ℝ))⁻¹ ^ m) := by
      intro j
      rw [Real.le_sqrt (norm_nonneg _) (pow_nonneg hpinv m)]
      by_cases hjm : j < m
      · rw [hvan j m hjm, norm_zero, pow_two, mul_zero]
        exact pow_nonneg hpinv m
      · have hmj : m ≤ j := by omega
        calc ‖e j m‖ ^ 2
            ≤ ‖(p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])‖ ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (hbound j m) 2
          _ ≤ ((p : ℝ))⁻¹ ^ j := sml_pow_div_factorial_norm p hp j
          _ ≤ ((p : ℝ))⁻¹ ^ m := pow_le_pow_of_le_one hpinv hp1le hmj
    have hS : ‖∑' j, e j m‖ ≤ Real.sqrt (((p : ℝ))⁻¹ ^ m) :=
      IsUltrametricDist.norm_tsum_le_of_forall_le hle
    calc ‖∑' j, e j m‖ ^ 2 ≤ (Real.sqrt (((p : ℝ))⁻¹ ^ m)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hS 2
      _ = ((p : ℝ))⁻¹ ^ m := Real.sq_sqrt (pow_nonneg hpinv m)
  refine ⟨fun m => ∑' j, e j m, ?_, ?_⟩
  · have hsq0 : Filter.Tendsto (fun m => ‖∑' j, e j m‖ ^ 2)
        Filter.cofinite (nhds 0) := by
      apply squeeze_zero (fun m => pow_nonneg (norm_nonneg _) 2)
        (fun m => hsq m)
      rw [Nat.cofinite_eq_atTop]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one hpinv hp1
    have h : Filter.Tendsto (fun m => Real.sqrt (‖∑' j, e j m‖ ^ 2))
        Filter.cofinite (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hsq0
    rw [Real.sqrt_zero] at h
    have hnorm : Filter.Tendsto (fun m => ‖∑' j, e j m‖)
        Filter.cofinite (nhds 0) :=
      Filter.Tendsto.congr (fun m => Real.sqrt_sq (norm_nonneg _)) h
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  · intro t
    have htt : ‖(t : ℚ_[p])‖ ≤ 1 := by
      have h : ‖(((t : ℤ)) : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one (t : ℤ)
      rwa [Int.cast_natCast] at h
    have httm : ∀ m : ℕ, ‖(t : ℚ_[p]) ^ m‖ ≤ 1 := by
      intro m
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) htt
    have hFbound : ∀ j m : ℕ,
        ‖e j m * (t : ℚ_[p]) ^ m‖
          ≤ ‖(p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])‖ := by
      intro j m
      calc ‖e j m * (t : ℚ_[p]) ^ m‖ = ‖e j m‖ * ‖(t : ℚ_[p]) ^ m‖ :=
            norm_mul _ _
        _ ≤ ‖(p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])‖ * 1 :=
            mul_le_mul (hbound j m) (httm m) (norm_nonneg _) (norm_nonneg _)
        _ = ‖(p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])‖ := mul_one _
    have hF0 : Filter.Tendsto
        (Function.uncurry fun j m => e j m * (t : ℚ_[p]) ^ m)
        Filter.cofinite (nhds 0) := by
      rw [Filter.tendsto_def]
      intro s hs
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
      have hball0 : Metric.ball (0 : ℝ) ε ∈ nhds (0 : ℝ) :=
        Metric.ball_mem_nhds _ hε
      have hev := hu0 hball0
      have hev2 : ∀ᶠ j in Filter.cofinite,
          (fun j => ‖(p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])‖) j
            ∈ Metric.ball (0 : ℝ) ε := hev
      have hfin : {j | ¬ ‖(p : ℚ_[p]) ^ j
          / ((Nat.factorial j : ℕ) : ℚ_[p])‖ < ε}.Finite :=
        Filter.eventually_cofinite.mp (hev2.mono fun j hj => by
          have hmem := Metric.mem_ball.mp hj
          rw [dist_zero_right, Real.norm_eq_abs,
            abs_of_nonneg (norm_nonneg _)] at hmem
          exact hmem)
      obtain ⟨J, hJ⟩ := Set.Finite.exists_finset_coe hfin
      have hsub : {q | ¬ Function.uncurry
            (fun j m => e j m * (t : ℚ_[p]) ^ m) q ∈ s}
          ⊆ ↑(J ×ˢ Finset.range (J.sup id + 1)) := by
        intro q hq
        obtain ⟨j, m⟩ := q
        have hq2 : ¬ e j m * (t : ℚ_[p]) ^ m ∈ s := hq
        have hge : ε ≤ ‖e j m * (t : ℚ_[p]) ^ m‖ := by
          by_contra hcon
          have hlt : ‖e j m * (t : ℚ_[p]) ^ m‖ < ε := lt_of_not_ge hcon
          have hmem : e j m * (t : ℚ_[p]) ^ m ∈ Metric.ball (0 : ℚ_[p]) ε :=
            Metric.mem_ball.mpr (by rwa [dist_zero_right])
          exact hq2 (hball hmem)
        have hjJ : j ∈ J := by
          have hle : ε
              ≤ ‖(p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])‖ :=
            le_trans hge (hFbound j m)
          have hnj : ¬ ‖(p : ℚ_[p]) ^ j
              / ((Nat.factorial j : ℕ) : ℚ_[p])‖ < ε := not_lt.mpr hle
          have hmem2 : j ∈ {j | ¬ ‖(p : ℚ_[p]) ^ j
              / ((Nat.factorial j : ℕ) : ℚ_[p])‖ < ε} := hnj
          rw [← hJ] at hmem2
          exact Finset.mem_coe.mp hmem2
        have hmj : m ≤ j := by
          by_contra hcon
          have hlt : j < m := lt_of_not_ge hcon
          have h0 : e j m * (t : ℚ_[p]) ^ m = 0 := by
            rw [hvan j m hlt, zero_mul]
          rw [h0] at hq2
          exact hq2 (mem_of_mem_nhds hs)
        have hle2 : j ≤ J.sup id := Finset.le_sup (f := id) hjJ
        have hmR : m ∈ Finset.range (J.sup id + 1) := by
          rw [Finset.mem_range]
          omega
        exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hjJ, hmR⟩)
      exact Filter.eventually_cofinite.mpr
        (Set.Finite.subset (Finset.finite_toSet _) hsub)
    have hFunc : Summable
        (Function.uncurry fun j m => e j m * (t : ℚ_[p]) ^ m) :=
      NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hF0
    have hrow : ∀ j : ℕ, Summable (fun m => e j m * (t : ℚ_[p]) ^ m) := by
      intro j
      apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      have hev : ∀ᶠ m in Filter.cofinite, e j m * (t : ℚ_[p]) ^ m = 0 := by
        apply Filter.eventually_cofinite.mpr
        apply Set.Finite.subset (Finset.finite_toSet (Finset.range (j + 1)))
        intro m hm
        rw [Finset.mem_coe, Finset.mem_range]
        by_contra hcon
        exact hm (by rw [hvan j m (by omega), zero_mul])
      exact Filter.Tendsto.congr' (hev.mono fun m hm => hm.symm)
        tendsto_const_nhds
    have hcol : ∀ m : ℕ, Summable (fun j => e j m * (t : ℚ_[p]) ^ m) := by
      intro m
      apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      exact squeeze_zero_norm (fun j => hFbound j m) hu0
    have hswap : (∑' m, ∑' j, e j m * (t : ℚ_[p]) ^ m)
        = (∑' j, ∑' m, e j m * (t : ℚ_[p]) ^ m) :=
      Summable.tsum_comm' hFunc hrow hcol
    have hinner : ∀ j : ℕ, (∑' m, e j m * (t : ℚ_[p]) ^ m)
        = (t.choose j : ℚ_[p]) * (p : ℚ_[p]) ^ j * w j := by
      intro j
      have hsupp : ∀ m ∉ Finset.range (j + 1),
          e j m * (t : ℚ_[p]) ^ m = 0 := by
        intro m hm
        rw [Finset.mem_range] at hm
        have hjm : j < m := by omega
        rw [hvan j m hjm, zero_mul]
      have hS1 : ∑ m ∈ Finset.range (j + 1), e j m * (t : ℚ_[p]) ^ m
          = ∑ m ∈ Finset.range (j + 1),
            ((((p : ℚ_[p]) ^ j / ((Nat.factorial j : ℕ) : ℚ_[p])) * w j)
              * ((((descPochhammer ℤ j).coeff m : ℤ) : ℚ_[p])
              * (t : ℚ_[p]) ^ m)) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [heq j m]
        ring
      have hpoly : ∑ m ∈ Finset.range (j + 1),
            ((((descPochhammer ℤ j).coeff m : ℤ)) : ℚ_[p]) * (t : ℚ_[p]) ^ m
          = (((t.descFactorial j : ℕ)) : ℚ_[p]) := by
        have hdeg : (((descPochhammer ℤ j).map
            (Int.castRingHom ℚ_[p])).natDegree) = j := by
          rw [descPochhammer_map, descPochhammer_natDegree]
        have hev : (((descPochhammer ℤ j).map
            (Int.castRingHom ℚ_[p])).eval (t : ℚ_[p]))
            = (((t.descFactorial j : ℕ)) : ℚ_[p]) := by
          rw [descPochhammer_map, descPochhammer_eval_eq_descFactorial]
        rw [← hev, Polynomial.eval_eq_sum_range, hdeg]
        apply Finset.sum_congr rfl
        intro m _
        rw [Polynomial.coeff_map, eq_intCast]
      have hfact0 : ((Nat.factorial j : ℕ) : ℚ_[p]) ≠ 0 := hfact j
      rw [tsum_eq_sum hsupp, hS1, ← Finset.mul_sum, hpoly,
        Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      field_simp
    have houter : (∑' j, ∑' m, e j m * (t : ℚ_[p]) ^ m)
        = ∑ j ∈ Finset.range (t + 1),
          (t.choose j : ℚ_[p]) * (p : ℚ_[p]) ^ j * w j := by
      trans ∑' j, ((t.choose j : ℚ_[p]) * (p : ℚ_[p]) ^ j * w j)
      · exact tsum_congr hinner
      · apply tsum_eq_sum
        intro j hj
        rw [Finset.mem_range] at hj
        have hjt : t < j := by omega
        rw [Nat.choose_eq_zero_of_lt hjt, Nat.cast_zero, zero_mul, zero_mul]
    have hpush : ∀ m : ℕ, (∑' j, e j m) * (t : ℚ_[p]) ^ m
        = ∑' j, e j m * (t : ℚ_[p]) ^ m :=
      fun m => ((hsum m).tsum_mul_right ((t : ℚ_[p]) ^ m)).symm
    change (∑' m, (∑' j, e j m) * (t : ℚ_[p]) ^ m)
      = ∑ j ∈ Finset.range (t + 1),
        (t.choose j : ℚ_[p]) * (p : ℚ_[p]) ^ j * w j
    calc (∑' m, (∑' j, e j m) * (t : ℚ_[p]) ^ m)
        = ∑' m, ∑' j, e j m * (t : ℚ_[p]) ^ m := tsum_congr hpush
      _ = ∑' j, ∑' m, e j m * (t : ℚ_[p]) ^ m := hswap
      _ = ∑ j ∈ Finset.range (t + 1),
          (t.choose j : ℚ_[p]) * (p : ℚ_[p]) ^ j * w j := houter

/-- The p-adic core — every residue class is zero or finite. -/
private theorem sml_padic_core (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (m : ℕ)
    (x γ : ℕ → ℤ_[p]) (hγ : IsUnit (γ 0))
    (hrec : ∀ n, x (n + (m + 1)) = ∑ i ∈ Finset.range (m + 1), γ i * x (n + i)) :
    ∃ N : ℕ, 0 < N ∧ ∀ a < N,
      (∀ t, x (a + N * t) = 0) ∨ (Set.Finite {t | x (a + N * t) = 0}) := by
  classical
  obtain ⟨A, hsA, hAunit⟩ := sml_companion p m x γ hγ hrec
  obtain ⟨N, hNpos, B, hAB⟩ := sml_period p m A hAunit
  refine ⟨N, hNpos, fun a _ => ?_⟩
  set s : ℕ → Fin (m + 1) → ℤ_[p] := fun n i => x (n + i.val)
  have hs' : ∀ n, s (n + 1) = A *ᵥ s n := fun n => hsA n
  have hN6 : ∀ t, s (a + N * t) = ∑ j ∈ Finset.range (t + 1),
      ((t.choose j : ℤ_[p])
        • ((((p : ℤ_[p]) ^ j) • (((B ^ j) *ᵥ s a))))) :=
    fun t => sml_binomial p m N s A B hs' hAB a t
  set w : ℕ → ℚ_[p] := fun j =>
    ((((B ^ j) *ᵥ s a) ⟨0, Nat.zero_lt_succ m⟩ : ℤ_[p]) : ℚ_[p])
  have hwnorm : ∀ j, ‖w j‖ ≤ 1 := fun j =>
    (((B ^ j) *ᵥ s a) ⟨0, Nat.zero_lt_succ m⟩).property
  obtain ⟨b, hb0, hbval⟩ := sml_series p hp w hwnorm
  have hcoord : ∀ t, s (a + N * t) ⟨0, Nat.zero_lt_succ m⟩
      = ∑ j ∈ Finset.range (t + 1),
        ((t.choose j : ℤ_[p])
          • ((((p : ℤ_[p]) ^ j)
            • (((B ^ j) *ᵥ s a) ⟨0, Nat.zero_lt_succ m⟩)))) := by
    intro t
    have h := congrFun (hN6 t) (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
    rw [Finset.sum_apply] at h
    simp only [Pi.smul_apply] at h
    exact h
  have hcoord' : ∀ t, x (a + N * t)
      = ∑ j ∈ Finset.range (t + 1),
        ((t.choose j : ℤ_[p]) * (p : ℤ_[p]) ^ j
          * (((B ^ j) *ᵥ s a) ⟨0, Nat.zero_lt_succ m⟩)) := by
    intro t
    have h0 : x (a + N * t) = s (a + N * t) ⟨0, Nat.zero_lt_succ m⟩ := rfl
    rw [h0, hcoord t]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_eq_mul, smul_eq_mul]
    ring
  have hwj : ∀ j : ℕ,
      (((((B ^ j) *ᵥ s a) ⟨0, Nat.zero_lt_succ m⟩ : ℤ_[p])) : ℚ_[p]) = w j :=
    fun j => rfl
  have hQ : ∀ t, ((((x (a + N * t) : ℤ_[p]))) : ℚ_[p])
      = ∑' m, b m * (t : ℚ_[p]) ^ m := by
    intro t
    rw [hcoord' t, PadicInt.coe_sum]
    simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, hwj]
    exact (hbval t).symm
  by_cases hbz : b = 0
  · left
    intro t
    have hb0m : ∀ m, b m = 0 := fun m => congrFun hbz m
    have h0 : ((((x (a + N * t) : ℤ_[p]))) : ℚ_[p]) = 0 := by
      rw [hQ t]
      have h00 : ∀ m, b m * (t : ℚ_[p]) ^ m = 0 := fun m => by
        rw [hb0m m, zero_mul]
      rw [tsum_congr h00, tsum_zero]
    exact PadicInt.coe_eq_zero.mp h0
  · right
    have hfin : {y : ℚ_[p] | ‖y‖ ≤ 1 ∧ ∑' m, b m * y ^ m = 0}.Finite :=
      Padic.strassmann p b hb0 hbz
    have htt2 : ∀ t : ℕ, ‖((t : ℕ) : ℚ_[p])‖ ≤ 1 := by
      intro t
      have h : ‖((((t : ℤ))) : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one (t : ℤ)
      rwa [Int.cast_natCast] at h
    have hsub : {t | x (a + N * t) = 0}
        ⊆ (fun t : ℕ => (t : ℚ_[p])) ⁻¹'
          {y : ℚ_[p] | ‖y‖ ≤ 1 ∧ ∑' m, b m * y ^ m = 0} := by
      intro t ht
      have ht0 : x (a + N * t) = 0 := ht
      change (t : ℚ_[p]) ∈ {y : ℚ_[p] | ‖y‖ ≤ 1 ∧ ∑' m, b m * y ^ m = 0}
      constructor
      · exact htt2 t
      · rw [← hQ t, ht0]
        simp
    have hpre : ((fun t : ℕ => (t : ℚ_[p])) ⁻¹'
        {y : ℚ_[p] | ‖y‖ ≤ 1 ∧ ∑' m, b m * y ^ m = 0}).Finite :=
      Set.Finite.preimage
        (Set.injOn_of_injective (@Nat.cast_injective ℚ_[p] _ _)) hfin
    exact Set.Finite.subset hpre hsub

/-- The nonzero-constant-coefficient case of Skolem–Mahler–Lech. -/
private theorem sml_main {K : Type*} [Field K] [CharZero K] (m : ℕ)
    (c u : ℕ → K) (hc0 : c 0 ≠ 0)
    (hrec : ∀ n, u (n + (m + 1)) =
      ∑ i ∈ Finset.range (m + 1), c i * u (n + i)) :
    ∃ (F : Finset ℕ) (P : Finset (ℕ × ℕ)), (∀ p ∈ P, 0 < p.2) ∧
      {n | u n = 0} = ↑F ∪ ⋃ p ∈ (↑P : Set (ℕ × ℕ)),
        {n | ∃ t, n = p.1 + p.2 * t} := by
  classical
  let I := Finset.range (m + 1)
  let S : Finset K := I.image c ∪ I.image u ∪ {(c 0)⁻¹}
  let R : Subring K := Subring.closure (↑S : Set K)
  have hcR : ∀ i < m + 1, c i ∈ R := by
    intro i hi
    apply Subring.subset_closure
    exact Finset.mem_coe.mpr <| Finset.mem_union_left _ <| Finset.mem_union_left _ <|
      Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
  have huR : ∀ i < m + 1, u i ∈ R := by
    intro i hi
    apply Subring.subset_closure
    exact Finset.mem_coe.mpr <| Finset.mem_union_left _ <| Finset.mem_union_right _ <|
      Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
  have hinvR : (c 0)⁻¹ ∈ R := by
    apply Subring.subset_closure
    exact Finset.mem_coe.mpr <| Finset.mem_union_right _ <| Finset.mem_singleton_self _
  have huAll : ∀ n, u n ∈ R := sml_closure_mem (m + 1) c u R hcR huR hrec
  obtain ⟨p, hp, hp3, phi, hphi⟩ :=
    Subring.exists_injective_ringHom_closure_padicInt S
  let _ : Fact p.Prime := ⟨hp⟩
  let ur : ℕ → R := fun n => ⟨u n, huAll n⟩
  let cr : ℕ → R := fun i =>
    if hi : i < m + 1 then ⟨c i, hcR i hi⟩ else 0
  have hcr : ∀ i < m + 1, ((cr i : R) : K) = c i := by
    intro i hi
    simp only [cr, dite_eq_left hi]
  have hrecR : ∀ n, ur (n + (m + 1)) =
      ∑ i ∈ Finset.range (m + 1), cr i * ur (n + i) := by
    intro n
    apply Subtype.ext
    change u (n + (m + 1)) = R.subtype
      (∑ i ∈ Finset.range (m + 1), cr i * ur (n + i))
    rw [map_sum, hrec]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_mul]
    change c i * u (n + i) = ((cr i : R) : K) * u (n + i)
    rw [hcr i (Finset.mem_range.mp hi)]
  let x : ℕ → ℤ_[p] := fun n => phi (ur n)
  let gamma : ℕ → ℤ_[p] := fun i => phi (cr i)
  have hrecP : ∀ n, x (n + (m + 1)) =
      ∑ i ∈ Finset.range (m + 1), gamma i * x (n + i) := by
    intro n
    change phi (ur (n + (m + 1))) =
      ∑ i ∈ Finset.range (m + 1), phi (cr i) * phi (ur (n + i))
    rw [hrecR n, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul]
  let cinv : R := ⟨(c 0)⁻¹, hinvR⟩
  have hprod : cr 0 * cinv = 1 := by
    apply Subtype.ext
    change c 0 * (c 0)⁻¹ = 1
    exact mul_inv_cancel₀ hc0
  have hgamma : IsUnit (gamma 0) := by
    apply IsUnit.of_mul_eq_one (phi cinv)
    change phi (cr 0) * phi cinv = 1
    rw [← map_mul, hprod, map_one]
  obtain ⟨N, hN, hclasses⟩ := sml_padic_core p hp3 m x gamma hgamma hrecP
  have hzero : ∀ n, x n = 0 ↔ u n = 0 := by
    intro n
    constructor
    · intro hx
      change phi (ur n) = 0 at hx
      have hur : ur n = 0 := hphi (hx.trans (map_zero phi).symm)
      calc
        u n = R.subtype (ur n) := rfl
        _ = R.subtype 0 := congrArg R.subtype hur
        _ = 0 := map_zero R.subtype
    · intro hu
      have hur : ur n = 0 := by
        apply Subtype.ext
        exact hu
      change phi (ur n) = 0
      rw [hur, map_zero]
  apply sml_assemble u N hN
  intro a ha
  rcases hclasses a ha with hall | hfinite
  · left
    intro t
    exact (hzero _).mp (hall t)
  · right
    have heq : {t | u (a + N * t) = 0} = {t | x (a + N * t) = 0} := by
      ext t
      exact (hzero _).symm
    rw [heq]
    exact hfinite

@[expose] public section

/-- **Skolem–Mahler–Lech theorem.** Let $K$ be a field of characteristic zero, let $k$ be a
natural number, let $c_0, \dots, c_{k-1} \in K$, and let $u_0, u_1, u_2, \dots$ be a sequence in
$K$ satisfying the linear recurrence $u_{n+k} = \sum_{i=0}^{k-1} c_i u_{n+i}$ for all $n \ge 0$
(for $k = 0$ the sum is empty and every $u_n$ is $0$). Then there are a finite set
$F \subseteq \mathbb{N}$ and finitely many pairs $(a_1, d_1), \dots, (a_m, d_m)$ of natural numbers
with every $d_j > 0$ such that the zero set of the sequence is
$$\{n \in \mathbb{N} : u_n = 0\} = F \cup \bigcup_{j=1}^{m} \{a_j + d_j t : t \in \mathbb{N}\}.$$

The proof follows Lech's $p$-adic method: the data embed in $\mathbb{Z}_p$ for a suitable prime $p$
(a Cassels-type embedding), on each residue class modulo the period of the companion matrix
modulo $p$ the sequence is given by a convergent $p$-adic power series, and Strassmann's theorem
bounds its zeros. C. Lech, A note on recurring series, Ark. Mat. 2 (1953), 417–421;
J. W. S. Cassels, An embedding theorem for fields, Bull. Austral. Math. Soc. 14 (1976), 193–198.

Proves `Wanted` entry `skolemMahlerLech`.

Source: https://en.wikipedia.org/wiki/Skolem%E2%80%93Mahler%E2%80%93Lech_theorem
(statement id `skolem-lech-s1`). -/
public theorem skolemMahlerLech {K : Type*} [Field K] [CharZero K]
    (k : ℕ) (c : ℕ → K) (u : ℕ → K)
    (hrec : ∀ n, u (n + k) = ∑ i ∈ Finset.range k, c i * u (n + i)) :
    ∃ (F : Finset ℕ) (P : Finset (ℕ × ℕ)), (∀ p ∈ P, 0 < p.2) ∧
      {n | u n = 0} = ↑F ∪ ⋃ p ∈ (↑P : Set (ℕ × ℕ)), {n | ∃ t, n = p.1 + p.2 * t} := by
  induction k generalizing c u with
  | zero =>
    have hu : ∀ n, u n = 0 := by
      intro n
      simpa using hrec n
    refine ⟨∅, {(0, 1)}, ?_, ?_⟩
    · simp
    · ext n
      simp [hu n]
  | succ m ih =>
    by_cases hc0 : c 0 = 0
    · let v : ℕ → K := fun n => u (n + 1)
      let c' : ℕ → K := fun i => c (i + 1)
      have hvrec : ∀ n, v (n + m) =
          ∑ i ∈ Finset.range m, c' i * v (n + i) := by
        intro n
        change u (n + m + 1) =
          ∑ i ∈ Finset.range m, c (i + 1) * u (n + i + 1)
        rw [show n + m + 1 = n + (m + 1) by omega, hrec n,
          Finset.sum_range_succ', hc0, zero_mul, add_zero]
        apply Finset.sum_congr rfl
        intro i _
        congr 1
      apply sml_shift u
      simpa only [v] using ih c' v hvrec
    · exact sml_main m c u hc0 hrec

end

end MetaMathlibExt
