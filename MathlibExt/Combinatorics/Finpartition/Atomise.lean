/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `306b05307ce5e07e232dc0c0f350c714e8df4107`.
Original formalization by Tsutomu Okano (@toskua) with Avocado (internal agent
identity); ported with permission.
-/

module

public import Mathlib.Order.Partition.Finpartition

@[expose] public section

open Finset

variable {α : Type*} [DecidableEq α]

namespace Finpartition

private theorem filter_atomise_singleton_eq {s B : Finset α}
    (hB : B ⊆ s) :
    (s.filter fun i =>
      ∀ u ∈ ({B} : Finset (Finset α)),
        u ∈ ({B} : Finset (Finset α)) ↔ i ∈ u) = B := by
  ext x
  constructor
  · intro hx
    have hall :
        ∀ u ∈ ({B} : Finset (Finset α)),
          u ∈ ({B} : Finset (Finset α)) ↔ x ∈ u :=
      (mem_filter.mp hx).2
    have hcond := hall B (mem_singleton_self B)
    simp only [mem_singleton, true_iff] at hcond
    exact hcond
  · intro hxB
    refine mem_filter.mpr ⟨hB hxB, ?_⟩
    intro u hu
    rw [mem_singleton] at hu
    subst hu
    simp only [mem_singleton, true_iff]
    exact hxB

private theorem filter_atomise_empty_eq {s B : Finset α} :
    (s.filter fun i =>
      ∀ u ∈ ({B} : Finset (Finset α)),
        u ∈ (∅ : Finset (Finset α)) ↔ i ∈ u) = s \ B := by
  ext x
  simp only [mem_filter, mem_sdiff]
  constructor
  · rintro ⟨hxs, hall⟩
    have hcond := hall B (mem_singleton_self B)
    simp only [notMem_empty, false_iff] at hcond
    exact ⟨hxs, hcond⟩
  · rintro ⟨hxs, hxB⟩
    refine ⟨hxs, ?_⟩
    intro u hu
    rw [mem_singleton] at hu
    subst hu
    simp only [notMem_empty, false_iff]
    exact hxB

theorem atomise_singleton_parts {s B : Finset α} (hB : B ⊆ s)
    (hBne : B.Nonempty) (hcompl : (s \ B).Nonempty) :
    (atomise s ({B} : Finset (Finset α))).parts = {B, s \ B} := by
  ext t
  simp only [mem_insert, mem_singleton]
  rw [mem_atomise]
  constructor
  · rintro ⟨_, Q, hQsub, hQeq⟩
    have hQcases : Q = ∅ ∨ Q = {B} := by
      rwa [Finset.subset_singleton_iff] at hQsub
    rcases hQcases with rfl | rfl
    · right
      exact hQeq.symm.trans filter_atomise_empty_eq
    · left
      exact hQeq.symm.trans (filter_atomise_singleton_eq hB)
  · intro ht
    rcases ht with h_eq | h_eq
    · rw [h_eq]
      exact ⟨hBne, {B}, Subset.rfl,
        filter_atomise_singleton_eq hB⟩
    · rw [h_eq]
      exact ⟨hcompl, ∅, empty_subset _,
        filter_atomise_empty_eq⟩

private theorem filter_atomise_compl_empty_eq {s B : Finset α} (hB : B ⊆ s) :
    (s.filter fun i =>
      ∀ u ∈ ((s \ B).map
        (⟨singleton, singleton_injective⟩ : α ↪ Finset α)),
        u ∈ (∅ : Finset (Finset α)) ↔ i ∈ u) = B := by
  ext x
  constructor
  · intro hx
    have hxs : x ∈ s := (mem_filter.mp hx).1
    have hall : ∀ u ∈ (s \ B).map (⟨singleton, singleton_injective⟩ : α ↪ Finset α),
        ¬ x ∈ u := by
      intro u hu
      have h := (mem_filter.mp hx).2 u hu
      simp only [notMem_empty, false_iff] at h
      exact h
    have h_not_in_compl : x ∉ s \ B := by
      intro hxC
      have hFmem : ({x} : Finset α) ∈
          (s \ B).map (⟨singleton, singleton_injective⟩ : α ↪ Finset α) := by
        rw [mem_map]
        exact ⟨x, hxC, rfl⟩
      have h_not : ¬ x ∈ ({x} : Finset α) := hall _ hFmem
      simp at h_not
    have hxB : x ∈ B := by
      by_contra hxNotB
      have hxC : x ∈ s \ B := mem_sdiff.mpr ⟨hxs, hxNotB⟩
      exact h_not_in_compl hxC
    exact hxB
  · intro hxB
    have hxs : x ∈ s := hB hxB
    refine mem_filter.mpr ⟨hxs, ?_⟩
    intro u hu
    rw [mem_map] at hu
    obtain ⟨y, hyC, rfl⟩ := hu
    have hyNotB : y ∉ B := (mem_sdiff.mp hyC).2
    have hxy : x ≠ y := by
      intro hxy
      subst hxy
      exact hyNotB hxB
    simp only [notMem_empty, false_iff]
    simp [hxy]

private theorem filter_atomise_compl_singleton_eq {s B : Finset α} {x : α}
    (hx : x ∈ s \ B) :
    (s.filter fun i =>
      ∀ u ∈ ((s \ B).map
        (⟨singleton, singleton_injective⟩ : α ↪ Finset α)),
        u ∈ ({ {x} } : Finset (Finset α)) ↔ i ∈ u) = {x} := by
  ext y
  constructor
  · intro hyF
    have hall := (mem_filter.mp hyF).2
    have hFx : ({x} : Finset α) ∈
        (s \ B).map (⟨singleton, singleton_injective⟩ : α ↪ Finset α) := by
      rw [mem_map]
      exact ⟨x, hx, rfl⟩
    have hcond := hall {x} hFx
    rw [mem_singleton] at hcond
    exact hcond.mp rfl
  · intro hyMem
    have hy_eq : y = x := mem_singleton.mp hyMem
    rw [hy_eq]
    have hys : x ∈ s := (mem_sdiff.mp hx).1
    refine mem_filter.mpr ⟨hys, ?_⟩
    intro u hu
    obtain ⟨z, _, rfl⟩ := mem_map.mp hu
    have hEmb : (⟨singleton, singleton_injective⟩ : α ↪ Finset α) z = {z} := rfl
    rw [hEmb]
    simp only [mem_singleton]
    constructor
    · intro hEq
      have hzx : z = x := singleton_inj.mp hEq
      exact hzx.symm
    · intro hEq
      have hzx : z = x := hEq.symm
      exact singleton_inj.mpr hzx

theorem atomise_compl_singletons_parts {s B : Finset α}
    (hB : B ⊆ s) (hBne : B.Nonempty) :
    (atomise s ((s \ B).map
      (⟨singleton, singleton_injective⟩ : α ↪ Finset α))).parts =
      insert B ((s \ B).map
        (⟨singleton, singleton_injective⟩ : α ↪ Finset α)) := by
  set C := s \ B
  set F := C.map (⟨singleton, singleton_injective⟩ : α ↪ Finset α)
  ext t
  rw [mem_atomise]
  constructor
  · rintro ⟨htNe, Q, hQsub, hQeq⟩
    have hQmemF : ∀ u ∈ Q, u ∈ F := fun u hu => hQsub hu
    have hExists : ∃ i, i ∈ s ∧ ∀ u ∈ F, (u ∈ Q ↔ i ∈ u) := by
      have hNe : (s.filter fun i => ∀ u ∈ F, u ∈ Q ↔ i ∈ u).Nonempty := by
        rw [hQeq]
        exact htNe
      obtain ⟨i, hi⟩ := hNe
      rw [mem_filter] at hi
      exact ⟨i, hi.1, hi.2⟩
    obtain ⟨i, hiS, hiCond⟩ := hExists
    have hQsmall : ∀ u1 ∈ Q, ∀ u2 ∈ Q, u1 = u2 := by
      intro u1 hu1 u2 hu2
      have h1 : i ∈ u1 := (hiCond u1 (hQmemF u1 hu1)).mp hu1
      have h2 : i ∈ u2 := (hiCond u2 (hQmemF u2 hu2)).mp hu2
      have hF1 : u1 ∈ F := hQmemF u1 hu1
      have hF2 : u2 ∈ F := hQmemF u2 hu2
      rw [mem_map] at hF1 hF2
      obtain ⟨y1, _, rfl⟩ := hF1
      obtain ⟨y2, _, rfl⟩ := hF2
      have hy1 : i = y1 := mem_singleton.mp h1
      have hy2 : i = y2 := mem_singleton.mp h2
      have hyEq : y1 = y2 := hy1.symm.trans hy2
      rw [hyEq]
    have hQcard : Q = ∅ ∨ ∃ x, Q = { {x} } ∧ x ∈ C := by
      by_cases hQempty : Q = ∅
      · left; exact hQempty
      · right
        have hQne : Q.Nonempty := by
          rw [nonempty_iff_ne_empty]
          exact hQempty
        obtain ⟨u, hu⟩ := hQne
        have huF : u ∈ F := hQsub hu
        rw [mem_map] at huF
        obtain ⟨x, hxC, hxEq⟩ := huF
        subst hxEq
        refine ⟨x, ?_, hxC⟩
        ext v
        simp only [mem_singleton]
        constructor
        · intro hv
          have := hQsmall v hv {x} hu
          exact this
        · intro hEq
          rw [hEq]
          exact hu
    rcases hQcard with hQempty | ⟨x, hQx, hxC⟩
    · have hBEq : (s.filter fun i => ∀ u ∈ F, u ∈ (∅ : Finset (Finset α)) ↔ i ∈ u) = B :=
        filter_atomise_compl_empty_eq hB
      have hTEq : t = B := by
        calc t = (s.filter fun i => ∀ u ∈ F, u ∈ Q ↔ i ∈ u) := hQeq.symm
          _ = (s.filter fun i => ∀ u ∈ F, u ∈ (∅ : Finset (Finset α)) ↔ i ∈ u) := by
              rw [hQempty]
          _ = B := hBEq
      rw [hTEq]
      exact mem_insert.mpr (Or.inl rfl)
    · have hFilterSingle :
          (s.filter fun i => ∀ u ∈ F, u ∈ ({ {x} } : Finset (Finset α)) ↔ i ∈ u) = {x} :=
        filter_atomise_compl_singleton_eq hxC
      have hTEq : t = {x} := by
        calc t = (s.filter fun i => ∀ u ∈ F, u ∈ Q ↔ i ∈ u) := hQeq.symm
          _ = (s.filter fun i => ∀ u ∈ F, u ∈ ({ {x} } : Finset (Finset α)) ↔ i ∈ u) := by
              rw [hQx]
          _ = {x} := hFilterSingle
      rw [hTEq]
      have hMem : ({x} : Finset α) ∈ F := by
        rw [mem_map]
        exact ⟨x, hxC, rfl⟩
      exact mem_insert.mpr (Or.inr hMem)
  · intro ht
    rw [mem_insert] at ht
    rcases ht with hEq | hMap
    · rw [hEq]
      refine ⟨hBne, ∅, empty_subset _, ?_⟩
      exact filter_atomise_compl_empty_eq hB
    · rw [mem_map] at hMap
      obtain ⟨x, hxC, hxEq⟩ := hMap
      have hEqT : t = {x} := by
        have hEmb : (⟨singleton, singleton_injective⟩ : α ↪ Finset α) x = {x} := rfl
        calc t = (⟨singleton, singleton_injective⟩ : α ↪ Finset α) x := hxEq.symm
          _ = {x} := hEmb
      rw [hEqT]
      have hSingNe : ({x} : Finset α).Nonempty := ⟨x, mem_singleton_self x⟩
      refine ⟨hSingNe, { {x} }, ?_, ?_⟩
      · intro v hv
        rw [mem_singleton] at hv
        rw [hv]
        rw [mem_map]
        exact ⟨x, hxC, rfl⟩
      · exact filter_atomise_compl_singleton_eq hxC

end Finpartition
