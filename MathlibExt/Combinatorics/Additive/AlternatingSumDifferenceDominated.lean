/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Alternating sum- and difference-dominated sets -/

namespace MetaMathlibExt

open scoped Pointwise

private def block (m d : ℤ) : Finset ℤ := (Finset.Icc 0 (m - 1)).erase d

private def core (m d k t : ℤ) : Finset ℤ :=
  block m d ∪ (Finset.Icc (-t) (k + t + 1)).image (fun j => j * m - d) ∪
    (block m d).image (fun b => (k + 1) * m - 2 * d - b)

private theorem mem_block (m d b : ℤ) :
    b ∈ block m d ↔ b ≠ d ∧ 0 ≤ b ∧ b ≤ m - 1 := by
  simp only [block, Finset.mem_erase, Finset.mem_Icc]

private theorem mem_core (m d k t a : ℤ) :
    a ∈ core m d k t ↔ a ∈ block m d ∨
      (∃ j : ℤ, -t ≤ j ∧ j ≤ k + t + 1 ∧ j * m - d = a) ∨
      ∃ b ∈ block m d, (k + 1) * m - 2 * d - b = a := by
  simp only [core, Finset.mem_union, Finset.mem_image, Finset.mem_Icc,
    or_assoc, and_assoc]

private structure Conditions (m d k : ℤ) : Prop where
  hm : 4 ≤ m
  hm4 : m % 4 = 0
  hd : 1 ≤ d
  hdm : d ≤ m - 1
  hd2 : 2 * d ≠ m
  quarter : 4 * d = m ∨ 4 * d = 3 * m
  hk3 : 2 * d < m → 3 ≤ k
  hk4 : m < 2 * d → 4 ≤ k

private theorem conditions {m d k : ℤ} (hm : 4 ≤ m) (hm4 : m % 4 = 0)
    (hd : 4 * d = m ∨ 4 * d = 3 * m)
    (hk3 : 2 * d < m → 3 ≤ k) (hk4 : m < 2 * d → 4 ≤ k) : Conditions m d k := by
  refine ⟨hm, hm4, ?_, ?_, ?_, hd, hk3, hk4⟩ <;> rcases hd with hd | hd <;> omega

private theorem Conditions.k_ge_three {m d k : ℤ} (h : Conditions m d k) : 3 ≤ k := by
  by_cases hd : 2 * d < m
  · exact h.hk3 hd
  · have hk := h.hk4 (by have he := h.hd2; omega)
    omega

private theorem residue_unique {m d b j : ℤ} (hm : 0 < m) (hd : 0 ≤ d)
    (hdm : d < m) (hb : 0 ≤ b) (hbm : b < m) (he : j * m + d = b) : b = d := by
  by_cases hj : j < 0
  · have hj' : j ≤ -1 := by omega
    nlinarith
  by_cases hj0 : j = 0
  · subst j
    simpa using he.symm
  · have hj' : 1 ≤ j := by omega
    nlinarith

private theorem reflect_core (m d k t a : ℤ) (ha : a ∈ core m d k t) :
    (k + 1) * m - 2 * d - a ∈ core m d k t := by
  rcases (mem_core m d k t a).mp ha with hb | ⟨j, hj, hjk, rfl⟩ | ⟨b, hb, rfl⟩
  · exact (mem_core _ _ _ _ _).mpr (Or.inr (Or.inr ⟨a, hb, rfl⟩))
  · have he : (k + 1) * m - 2 * d - (j * m - d) = (k + 1 - j) * m - d := by
      ring
    rw [he]
    exact (mem_core _ _ _ _ _).mpr (Or.inr (Or.inl ⟨k + 1 - j,
      by omega, by omega, rfl⟩))
  · rw [show (k + 1) * m - 2 * d - ((k + 1) * m - 2 * d - b) = b by omega]
    exact (mem_core _ _ _ _ _).mpr (Or.inl hb)

private theorem block_mem_core {m d k t b : ℤ} (hb : b ∈ block m d) :
    b ∈ core m d k t := (mem_core _ _ _ _ _).mpr (Or.inl hb)

private theorem spine_mem_core {m d k t j : ℤ} (hj : -t ≤ j)
    (hjk : j ≤ k + t + 1) : j * m - d ∈ core m d k t :=
  (mem_core _ _ _ _ _).mpr (Or.inr (Or.inl ⟨j, hj, hjk, rfl⟩))

private theorem reflected_mem_core {m d k t b : ℤ} (hb : b ∈ block m d) :
    (k + 1) * m - 2 * d - b ∈ core m d k t :=
  (mem_core _ _ _ _ _).mpr (Or.inr (Or.inr ⟨b, hb, rfl⟩))

private theorem reflected_gt {m d k b : ℤ} (h : Conditions m d k)
    (hb : b ∈ block m d) : 2 * m < (k + 1) * m - 2 * d - b := by
  have hm := h.hm
  have hdm := h.hdm
  have hb' := (mem_block _ _ _).mp hb
  by_cases hd : 2 * d < m
  · have hk := h.hk3 hd
    nlinarith
  · have hd2 := h.hd2
    have hk := h.hk4 (by omega)
    nlinarith

private theorem no_double_hole {m d k : ℤ} (h : Conditions m d k) (j : ℤ) :
    j * m ≠ 2 * d := by
  have hm := h.hm
  have hd := h.hd
  have hdm := h.hdm
  intro he
  by_cases hj : j ≤ 0
  · nlinarith
  by_cases hj1 : j = 1
  · subst j
    exact h.hd2 (by omega)
  · have hj2 : 2 ≤ j := by omega
    nlinarith

private theorem block_spine_ne {m d k b : ℤ} (h : Conditions m d k)
    (hb : b ∈ block m d) (j : ℤ) : b + (j * m - d) ≠ 2 * m := by
  have hb' := (mem_block _ _ _).mp hb
  intro he
  have hm : 0 < m := by have hm := h.hm; omega
  have hd : 0 ≤ d := by have hd := h.hd; omega
  have hdm : d < m := by have hdm := h.hdm; omega
  have he' : (2 - j) * m + d = b := by nlinarith
  have hb_eq := residue_unique hm hd hdm hb'.2.1 (by omega) he'
  exact hb'.1 hb_eq

private theorem spine_reflected_ne {m d k b : ℤ} (h : Conditions m d k)
    (hb : b ∈ block m d) (j : ℤ) :
    (j * m - d) + ((k + 1) * m - 2 * d - b) ≠ 2 * m := by
  have hb' := (mem_block _ _ _).mp hb
  have hm : 0 < m := by have hm := h.hm; omega
  have hd : 0 ≤ d := by have hd := h.hd; omega
  have hdm : d < m := by have hdm := h.hdm; omega
  intro he
  rcases h.quarter with hq | hq
  · have he' : (j + k - 2) * m + d = b := by nlinarith
    exact hb'.1 (residue_unique hm hd hdm hb'.2.1 (by omega) he')
  · have he' : (j + k - 4) * m + d = b := by nlinarith
    exact hb'.1 (residue_unique hm hd hdm hb'.2.1 (by omega) he')

private theorem two_mul_notMem_core_add {m d k t : ℤ} (h : Conditions m d k) :
    2 * m ∉ core m d k t + core m d k t := by
  intro hz
  obtain ⟨a, ha, b, hb, he⟩ := Finset.mem_add.mp hz
  rcases (mem_core _ _ _ _ _).mp ha with ha | ⟨i, _, _, rfl⟩ | ⟨u, hu, rfl⟩
  · rcases (mem_core _ _ _ _ _).mp hb with hb | ⟨j, _, _, rfl⟩ | ⟨v, hv, rfl⟩
    · have ha' := (mem_block _ _ _).mp ha
      have hb' := (mem_block _ _ _).mp hb
      omega
    · exact block_spine_ne h ha j he
    · have ha' := (mem_block _ _ _).mp ha
      have hv' := reflected_gt h hv
      omega
  · rcases (mem_core _ _ _ _ _).mp hb with hb | ⟨j, _, _, rfl⟩ | ⟨v, hv, rfl⟩
    · exact block_spine_ne h hb i (by omega)
    · apply no_double_hole h (i + j - 2)
      nlinarith
    · exact spine_reflected_ne h hv i he
  · rcases (mem_core _ _ _ _ _).mp hb with hb | ⟨j, _, _, rfl⟩ | ⟨v, hv, rfl⟩
    · have hb' := (mem_block _ _ _).mp hb
      have hu' := reflected_gt h hu
      omega
    · exact spine_reflected_ne h hu j (by omega)
    · have hu' := reflected_gt h hu
      have hv' := reflected_gt h hv
      have hm := h.hm
      omega

private theorem add_block_mem_core_add {m d k t b : ℤ} (h : Conditions m d k)
    (ht : 0 ≤ t) (hb : b ∈ block m d) : m + b ∈ core m d k t + core m d k t := by
  have hm := h.hm
  have hd := h.hd
  have hdm := h.hdm
  have hk := h.k_ge_three
  have hb' := (mem_block _ _ _).mp hb
  by_cases hb0 : b = 0
  · subst b
    by_cases hend : d = 1 ∨ d = m - 1
    · exact Finset.mem_add.mpr ⟨2, block_mem_core ((mem_block _ _ _).mpr (by omega)),
        m - 2, block_mem_core ((mem_block _ _ _).mpr (by omega)), by omega⟩
    · exact Finset.mem_add.mpr ⟨1, block_mem_core ((mem_block _ _ _).mpr (by omega)),
        m - 1, block_mem_core ((mem_block _ _ _).mpr (by omega)), by omega⟩
  · by_cases hlow : b + d < m
    · exact Finset.mem_add.mpr ⟨1 * m - d, spine_mem_core (by omega) (by omega),
        b + d, block_mem_core ((mem_block _ _ _).mpr (by omega)), by omega⟩
    · exact Finset.mem_add.mpr ⟨2 * m - d, spine_mem_core (by omega) (by omega),
        b + d - m, block_mem_core ((mem_block _ _ _).mpr (by omega)), by omega⟩

private theorem endpoint_add_block_mem {m d k t b : ℤ} (h : Conditions m d k)
    (ht : 0 ≤ t) (hb : b ∈ block m d ∨ b = m) :
    (k + t + 2) * m - d + b ∈ core m d k t + core m d k t := by
  have hm := h.hm
  have hd := h.hd
  have hdm := h.hdm
  have hb' : b ≠ d ∧ 0 ≤ b ∧ b ≤ m := by
    rcases hb with hb | rfl
    · have he := (mem_block _ _ _).mp hb
      omega
    · omega
  rcases h.quarter with hq | hq
  · have hk := h.hk3 (by omega)
    by_cases hlow : b ≤ m - 2 * d
    · exact Finset.mem_add.mpr ⟨(t + 2) * m - d,
        spine_mem_core (by omega) (by omega),
        (k + 1) * m - 2 * d - (m - 2 * d - b),
        reflected_mem_core ((mem_block _ _ _).mpr (by omega)), by ring⟩
    · exact Finset.mem_add.mpr ⟨(t + 3) * m - d,
        spine_mem_core (by omega) (by omega),
        (k + 1) * m - 2 * d - (2 * m - 2 * d - b),
        reflected_mem_core ((mem_block _ _ _).mpr (by omega)), by ring⟩
  · have hk := h.hk4 (by omega)
    by_cases hlow : b ≤ 2 * m - 2 * d
    · exact Finset.mem_add.mpr ⟨(t + 3) * m - d,
        spine_mem_core (by omega) (by omega),
        (k + 1) * m - 2 * d - (2 * m - 2 * d - b),
        reflected_mem_core ((mem_block _ _ _).mpr (by omega)), by ring⟩
    · exact Finset.mem_add.mpr ⟨(t + 4) * m - d,
        spine_mem_core (by omega) (by omega),
        (k + 1) * m - 2 * d - (3 * m - 2 * d - b),
        reflected_mem_core ((mem_block _ _ _).mpr (by omega)), by ring⟩

private theorem add_reflected_mem {m d k t b : ℤ} (h : Conditions m d k)
    (ht : 0 ≤ t) (hb : b ∈ block m d) :
    m + ((k + 1) * m - 2 * d - b) ∈ core m d k t + core m d k t := by
  have hm := h.hm
  have hd := h.hd
  have hdm := h.hdm
  have hk := h.k_ge_three
  have hb' := (mem_block _ _ _).mp hb
  have h0 : 0 ∈ block m d := (mem_block _ _ _).mpr (by omega)
  by_cases hb0 : b = 0
  · subst b
    exact Finset.mem_add.mpr ⟨(k + 1) * m - d, spine_mem_core (by omega) (by omega),
      1 * m - d, spine_mem_core (by omega) (by omega), by ring⟩
  by_cases he : m - b = d
  · exact Finset.mem_add.mpr ⟨(k + 1) * m - d, spine_mem_core (by omega) (by omega),
      0, block_mem_core h0, by omega⟩
  · exact Finset.mem_add.mpr ⟨(k + 1) * m - 2 * d - 0, reflected_mem_core h0,
      m - b, block_mem_core ((mem_block _ _ _).mpr (by omega)), by ring⟩

private theorem add_spine_mem {m d k t j : ℤ} (h : Conditions m d k)
    (ht : 0 ≤ t) (hj : -t ≤ j) (hjk : j ≤ k + t + 1) :
    m + (j * m - d) ∈ core m d k t + core m d k t := by
  have hd := h.hd
  have hm := h.hm
  have h0 : 0 ∈ block m d := (mem_block _ _ _).mpr (by omega)
  by_cases he : j = k + t + 1
  · subst j
    convert endpoint_add_block_mem h ht (Or.inl h0) using 1
    ring
  · exact Finset.mem_add.mpr ⟨(j + 1) * m - d, spine_mem_core (by omega) (by omega),
      0, block_mem_core h0, by ring⟩

private theorem add_core_subset {m d k t : ℤ} (h : Conditions m d k) (ht : 0 ≤ t) :
    {m} + core m d k t ⊆ core m d k t + core m d k t := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
  rw [Finset.mem_singleton.mp ha]
  rcases (mem_core _ _ _ _ _).mp hb with hb | ⟨j, hj, hjk, rfl⟩ | ⟨x, hx, rfl⟩
  · exact add_block_mem_core_add h ht hb
  · exact add_spine_mem h ht hj hjk
  · exact add_reflected_mem h ht hx

private theorem sub_core_subset {m d k t : ℤ} (h : Conditions m d k) (ht : 0 ≤ t) :
    {m} - core m d k t ⊆ core m d k t - core m d k t := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
  rw [Finset.mem_singleton.mp ha]
  have hr := reflect_core m d k t b hb
  obtain ⟨u, hu, v, hv, he⟩ := Finset.mem_add.mp
    (add_core_subset h ht (Finset.mem_add.mpr ⟨m, by simp,
      (k + 1) * m - 2 * d - b, hr, rfl⟩))
  exact Finset.mem_sub.mpr ⟨u, hu, (k + 1) * m - 2 * d - v,
    reflect_core m d k t v hv, by omega⟩

private theorem core_add_card (m d k t : ℤ) :
    (core m d k t + core m d k t).card = (core m d k t - core m d k t).card := by
  apply Nat.le_antisymm
  · apply Finset.card_le_card_of_injOn (fun z : ℤ => z - ((k + 1) * m - 2 * d))
    · intro z hz
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hz
      exact Finset.mem_sub.mpr ⟨u, hu, (k + 1) * m - 2 * d - v,
        reflect_core m d k t v hv, by dsimp only; omega⟩
    · intro u _ v _ he
      dsimp only at he
      omega
  · apply Finset.card_le_card_of_injOn (fun z : ℤ => (k + 1) * m - 2 * d + z)
    · intro z hz
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hz
      exact Finset.mem_add.mpr ⟨u, hu, (k + 1) * m - 2 * d - v,
        reflect_core m d k t v hv, by dsimp only; omega⟩
    · intro u _ v _ he
      dsimp only at he
      omega

private theorem zero_mem_core {m d k t : ℤ} (h : Conditions m d k) :
    0 ∈ core m d k t := by
  have hm := h.hm
  have hd := h.hd
  exact block_mem_core ((mem_block _ _ _).mpr (by omega))

private theorem m_notMem_core {m d k t : ℤ} (h : Conditions m d k) :
    m ∉ core m d k t := by
  intro hm
  exact two_mul_notMem_core_add h (Finset.mem_add.mpr ⟨m, hm, m, hm, by omega⟩)

private theorem odd_add {m d k t : ℤ} (h : Conditions m d k) (ht : 0 ≤ t) :
    insert m (core m d k t) + insert m (core m d k t) =
      insert (2 * m) (core m d k t + core m d k t) := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
    rcases Finset.mem_insert.mp ha with ham | ha
    · subst a
      rcases Finset.mem_insert.mp hb with hbm | hb
      · subst b
        simp [two_mul]
      · exact Finset.mem_insert.mpr (Or.inr
          (add_core_subset h ht (Finset.mem_add.mpr ⟨m, by simp, b, hb, rfl⟩)))
    · rcases Finset.mem_insert.mp hb with hbm | hb
      · subst b
        exact Finset.mem_insert.mpr (Or.inr
          (add_core_subset h ht (Finset.mem_add.mpr ⟨m, by simp, a, ha, by omega⟩)))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.add_mem_add ha hb))
  · intro hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · subst z
      exact Finset.mem_add.mpr ⟨m, by simp, m, by simp, by omega⟩
    · exact Finset.add_subset_add (Finset.subset_insert _ _) (Finset.subset_insert _ _) hz

private theorem odd_sub {m d k t : ℤ} (h : Conditions m d k) (ht : 0 ≤ t) :
    insert m (core m d k t) - insert m (core m d k t) =
      core m d k t - core m d k t := by
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
    rcases Finset.mem_insert.mp ha with ham | ha
    · subst a
      rcases Finset.mem_insert.mp hb with hbm | hb
      · subst b
        exact Finset.mem_sub.mpr ⟨0, zero_mem_core h, 0, zero_mem_core h, by omega⟩
      · exact sub_core_subset h ht (Finset.mem_sub.mpr ⟨m, by simp, b, hb, rfl⟩)
    · rcases Finset.mem_insert.mp hb with hbm | hb
      · subst b
        obtain ⟨u, hu, v, hv, he⟩ := Finset.mem_sub.mp
          (sub_core_subset h ht (Finset.mem_sub.mpr ⟨m, by simp, a, ha, rfl⟩))
        exact Finset.mem_sub.mpr ⟨v, hv, u, hu, by omega⟩
      · exact Finset.sub_mem_sub ha hb
  · exact Finset.sub_subset_sub (Finset.subset_insert _ _) (Finset.subset_insert _ _)

private theorem odd_card {m d k t : ℤ} (h : Conditions m d k) (ht : 0 ≤ t) :
    (insert m (core m d k t) + insert m (core m d k t)).card =
      (insert m (core m d k t) - insert m (core m d k t)).card + 1 := by
  rw [odd_add h ht, odd_sub h ht, Finset.card_insert_of_notMem (two_mul_notMem_core_add h),
    core_add_card]

private theorem endpoint_spine_add_mem {m d k t j : ℤ} (hj : -t ≤ j) (hjk : j < k + t + 1) :
    ((k + t + 2) * m - d) + (j * m - d) ∈ core m d k t + core m d k t := by
  exact Finset.mem_add.mpr ⟨(j + 1) * m - d, spine_mem_core (by omega) (by omega),
    (k + t + 1) * m - d, spine_mem_core (by omega) (by omega), by ring⟩

private def newSums (m d k t : ℤ) : Finset ℤ :=
  let p := (k + t + 2) * m - d
  insert (2 * p) (insert (p + ((k + t + 1) * m - d))
    (((block m d).erase (m - d)).image (fun b => p + ((k + 1) * m - 2 * d - b))))

private theorem endpoint_add_mem {m d k t a : ℤ} (h : Conditions m d k)
    (ht : 0 ≤ t) (ha : a ∈ insert m (core m d k t)) :
    (k + t + 2) * m - d + a ∈
      (insert m (core m d k t) + insert m (core m d k t)) ∪ newSums m d k t := by
  have hkeep : core m d k t + core m d k t ⊆
      insert m (core m d k t) + insert m (core m d k t) :=
    Finset.add_subset_add (Finset.subset_insert _ _) (Finset.subset_insert _ _)
  rcases Finset.mem_insert.mp ha with ham | ha
  · subst a
    exact Finset.mem_union.mpr (Or.inl (hkeep (endpoint_add_block_mem h ht (Or.inr rfl))))
  rcases (mem_core _ _ _ _ _).mp ha with hb | ⟨j, hj, hjk, rfl⟩ | ⟨b, hb, rfl⟩
  · exact Finset.mem_union.mpr (Or.inl (hkeep (endpoint_add_block_mem h ht (Or.inl hb))))
  · by_cases he : j = k + t + 1
    · subst j
      exact Finset.mem_union.mpr (Or.inr (by simp [newSums]))
    · exact Finset.mem_union.mpr
        (Or.inl (hkeep (endpoint_spine_add_mem hj (by omega))))
  · by_cases he : b = m - d
    · subst b
      have hk := h.k_ge_three
      have hz := endpoint_spine_add_mem (m := m) (d := d) (k := k) (t := t) (j := k)
        (by omega) (by omega)
      exact Finset.mem_union.mpr (Or.inl (hkeep (by convert hz using 1; ring)))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr
        (Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
          ⟨b, Finset.mem_erase.mpr ⟨he, hb⟩, rfl⟩))))))

private theorem even_add_subset {m d k t : ℤ} (h : Conditions m d k) (ht : 0 ≤ t) :
    let S := insert m (core m d k t)
    let p := (k + t + 2) * m - d
    insert p S + insert p S ⊆ (S + S) ∪ newSums m d k t := by
  intro S p z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
  rcases Finset.mem_insert.mp ha with hap | ha
  · subst a
    rcases Finset.mem_insert.mp hb with hbp | hb
    · subst b
      exact Finset.mem_union.mpr (Or.inr (by simp [newSums, p, two_mul]))
    · exact endpoint_add_mem h ht hb
  · rcases Finset.mem_insert.mp hb with hbp | hb
    · subst b
      simpa only [add_comm] using endpoint_add_mem h ht ha
    · exact Finset.mem_union.mpr (Or.inl (Finset.add_mem_add ha hb))

private theorem block_card {m d k : ℤ} (h : Conditions m d k) :
    ((block m d).card : ℤ) = m - 1 := by
  have hm := h.hm
  have hd := h.hd
  have hdm := h.hdm
  have hdmem : d ∈ Finset.Icc 0 (m - 1) := by simp only [Finset.mem_Icc]; omega
  have hc := Finset.card_erase_add_one hdmem
  rw [Int.card_Icc] at hc
  change (block m d).card + 1 = (m - 1 + 1 - 0).toNat at hc
  omega

private theorem newSums_card {m d k t : ℤ} (h : Conditions m d k) :
    ((newSums m d k t).card : ℤ) ≤ m := by
  have hm := h.hm
  have hd := h.hd
  have hdm := h.hdm
  have hd2 := h.hd2
  have hb : m - d ∈ block m d := (mem_block _ _ _).mpr (by omega)
  have hc := Finset.card_erase_add_one hb
  have hB := block_card h
  let p := (k + t + 2) * m - d
  let U := ((block m d).erase (m - d)).image (fun b => p + ((k + 1) * m - 2 * d - b))
  have hU : U.card ≤ ((block m d).erase (m - d)).card := Finset.card_image_le
  have h1 := Finset.card_insert_le (2 * p) (insert (p + ((k + t + 1) * m - d)) U)
  have h2 := Finset.card_insert_le (p + ((k + t + 1) * m - d)) U
  change ((insert (2 * p) (insert (p + ((k + t + 1) * m - d)) U)).card : ℤ) ≤ m
  omega

private theorem even_add_card {m d k t : ℤ} (h : Conditions m d k) (ht : 0 ≤ t) :
    let S := insert m (core m d k t)
    let p := (k + t + 2) * m - d
    ((insert p S + insert p S).card : ℤ) ≤ (S + S).card + m := by
  intro S p
  have h1 := Finset.card_le_card (even_add_subset h ht)
  change (insert p S + insert p S).card ≤ ((S + S) ∪ newSums m d k t).card at h1
  have h2 := Finset.card_union_le (S + S) (newSums m d k t)
  have h3 := newSums_card (t := t) h
  omega

private theorem core_upper {m d k t a : ℤ} (h : Conditions m d k) (ht : 0 ≤ t)
    (ha : a ∈ core m d k t) : a ≤ (k + t + 1) * m - d := by
  have hm := h.hm
  have hd := h.hd
  have hdm := h.hdm
  have hk := h.k_ge_three
  rcases (mem_core _ _ _ _ _).mp ha with hb | ⟨j, hj, hjk, rfl⟩ | ⟨b, hb, rfl⟩
  · have hb' := (mem_block _ _ _).mp hb
    nlinarith
  · nlinarith
  · have hb' := (mem_block _ _ _).mp hb
    nlinarith

private theorem core_lower {m d k t a : ℤ} (h : Conditions m d k) (ht : 0 ≤ t)
    (ha : a ∈ core m d k t) : -t * m - d ≤ a := by
  have hr := core_upper h ht (reflect_core m d k t a ha)
  nlinarith

private theorem odd_bounds {m d k t a : ℤ} (h : Conditions m d k) (ht : 0 ≤ t)
    (ha : a ∈ insert m (core m d k t)) :
    -t * m - d ≤ a ∧ a ≤ (k + t + 1) * m - d := by
  rcases Finset.mem_insert.mp ha with ham | ha
  · subst a
    have hm := h.hm
    have hd := h.hd
    have hdm := h.hdm
    have hk := h.k_ge_three
    constructor <;> nlinarith
  · exact ⟨core_lower h ht ha, core_upper h ht ha⟩

private theorem large_core_difference {m d k t z : ℤ} (h : Conditions m d k)
    (ht : 0 ≤ t) (hz : z ∈ core m d k t - core m d k t)
    (hlarge : (k + t + 1) * m - d < z) : ∃ j : ℤ, z = j * m := by
  have hm := h.hm
  have hd := h.hd
  have hdm := h.hdm
  have hk := h.k_ge_three
  obtain ⟨a, ha, b, hb, he⟩ := Finset.mem_sub.mp hz
  have hau := core_upper h ht ha
  have hbl := core_lower h ht hb
  rcases (mem_core _ _ _ _ _).mp ha with ha | ⟨i, _, _, rfl⟩ | ⟨u, hu, rfl⟩
  · have ha' := (mem_block _ _ _).mp ha
    exfalso
    nlinarith
  · rcases (mem_core _ _ _ _ _).mp hb with hb | ⟨j, _, _, rfl⟩ | ⟨v, hv, rfl⟩
    · have hb' := (mem_block _ _ _).mp hb
      exfalso
      omega
    · exact ⟨i - j, by nlinarith⟩
    · have hv' := reflected_gt h hv
      exfalso
      omega
  · rcases (mem_core _ _ _ _ _).mp hb with hb | ⟨j, hj, hjk, rfl⟩ | ⟨v, hv, rfl⟩
    · have hb' := (mem_block _ _ _).mp hb
      exfalso
      omega
    · have hu' := (mem_block _ _ _).mp hu
      have hr := core_upper h ht (reflect_core m d k t (j * m - d)
        (spine_mem_core hj hjk))
      exfalso
      omega
    · have hv' := reflected_gt h hv
      exfalso
      omega

private theorem multiple_between {m j z : ℤ} (hm : 0 < m) (hz : 0 < z)
    (hz2 : z < 2 * m) (he : j * m = z) : z = m := by
  by_cases hj : j ≤ 0
  · nlinarith
  by_cases hj1 : j = 1
  · subst j
    simpa using he.symm
  · have hj2 : 2 ≤ j := by omega
    nlinarith

private def newPositiveDifferences (m d k t : ℤ) : Finset ℤ :=
  insert ((k + 2 * t + 2) * m)
    (((block m d).erase (m - d)).image (fun b => (k + t + 2) * m - d - b))

private theorem newPositiveDifferences_pos {m d k t z : ℤ} (h : Conditions m d k)
    (ht : 0 ≤ t) (hz : z ∈ newPositiveDifferences m d k t) : 0 < z := by
  have hm := h.hm
  have hd := h.hd
  have hdm := h.hdm
  have hk := h.k_ge_three
  rcases Finset.mem_insert.mp hz with hz | hz
  · subst z
    nlinarith
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
    have hb' := (mem_block _ _ _).mp (Finset.mem_erase.mp hb).2
    nlinarith

private theorem newPositiveDifferences_notMem {m d k t z : ℤ} (h : Conditions m d k)
    (ht : 0 ≤ t) (hz : z ∈ newPositiveDifferences m d k t) :
    z ∉ insert m (core m d k t) - insert m (core m d k t) := by
  have hm := h.hm
  have hd := h.hd
  have hdm := h.hdm
  rcases Finset.mem_insert.mp hz with hz | hz
  · subst z
    intro hzold
    obtain ⟨u, hu, v, hv, he⟩ := Finset.mem_sub.mp hzold
    have hu' := odd_bounds h ht hu
    have hv' := odd_bounds h ht hv
    nlinarith
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
    have hbn := (Finset.mem_erase.mp hb).1
    have hb' := (mem_block _ _ _).mp (Finset.mem_erase.mp hb).2
    intro hzold
    rw [odd_sub h ht] at hzold
    obtain ⟨j, hj⟩ := large_core_difference h ht hzold (by nlinarith)
    have he : (k + t + 2 - j) * m = d + b := by nlinarith
    have hb_eq := multiple_between (m := m) (by omega) (by omega) (by omega) he
    exact hbn (by omega)

private theorem newPositiveDifferences_mem {m d k t z : ℤ} (h : Conditions m d k)
    (ht : 0 ≤ t) (hz : z ∈ newPositiveDifferences m d k t) :
    let S := insert m (core m d k t)
    let p := (k + t + 2) * m - d
    z ∈ insert p S - insert p S := by
  intro S p
  rcases Finset.mem_insert.mp hz with hz | hz
  · subst z
    have hk := h.k_ge_three
    exact Finset.mem_sub.mpr ⟨p, by simp, -t * m - d,
      Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (spine_mem_core (by omega) (by omega))))), by dsimp only [p]; ring⟩
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_sub.mpr ⟨p, by simp, b,
      Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (block_mem_core (Finset.mem_erase.mp hb).2)))), rfl⟩

private theorem newPositiveDifferences_card {m d k t : ℤ} (h : Conditions m d k)
    (ht : 0 ≤ t) : ((newPositiveDifferences m d k t).card : ℤ) = m - 1 := by
  have hm := h.hm
  have hd := h.hd
  have hdm := h.hdm
  have hd2 := h.hd2
  have hb : m - d ∈ block m d := (mem_block _ _ _).mpr (by omega)
  have hc := Finset.card_erase_add_one hb
  have hB := block_card h
  let V := ((block m d).erase (m - d)).image (fun b => (k + t + 2) * m - d - b)
  have hV : V.card = ((block m d).erase (m - d)).card :=
    Finset.card_image_of_injective _ (by
      intro x y he
      change (k + t + 2) * m - d - x = (k + t + 2) * m - d - y at he
      omega)
  have hn : (k + 2 * t + 2) * m ∉ V := by
    intro hz
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hz
    have hb' := (mem_block _ _ _).mp (Finset.mem_erase.mp hb).2
    nlinarith
  have he := Finset.card_insert_of_notMem hn
  change (newPositiveDifferences m d k t).card = V.card + 1 at he
  omega

private theorem neg_mem_difference {S : Finset ℤ} {z : ℤ} (hz : z ∈ S - S) :
    -z ∈ S - S := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
  exact Finset.mem_sub.mpr ⟨b, hb, a, ha, by omega⟩

private theorem even_sub_card {m d k t : ℤ} (h : Conditions m d k) (ht : 0 ≤ t) :
    let S := insert m (core m d k t)
    let p := (k + t + 2) * m - d
    (S - S).card + 2 * m - 2 ≤ ((insert p S - insert p S).card : ℤ) := by
  intro S p
  let D := S - S
  let P := newPositiveDifferences m d k t
  let N := P.image (fun z => -z)
  have hNP (z : ℤ) (hz : z ∈ N) : -z ∈ P := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    simpa only [neg_neg] using hu
  have hDP : Disjoint D P := Finset.disjoint_left.mpr (by
    intro z hzD hzP
    exact newPositiveDifferences_notMem h ht hzP hzD)
  have hDN : Disjoint D N := Finset.disjoint_left.mpr (by
    intro z hzD hzN
    exact newPositiveDifferences_notMem h ht (hNP z hzN) (neg_mem_difference hzD))
  have hPN : Disjoint P N := Finset.disjoint_left.mpr (by
    intro z hzP hzN
    have hp := newPositiveDifferences_pos h ht hzP
    have hn := newPositiveDifferences_pos h ht (hNP z hzN)
    omega)
  have hUN : Disjoint (D ∪ P) N := Finset.disjoint_left.mpr (by
    intro z hz hzN
    rcases Finset.mem_union.mp hz with hzD | hzP
    · exact Finset.disjoint_left.mp hDN hzD hzN
    · exact Finset.disjoint_left.mp hPN hzP hzN)
  have hsub : (D ∪ P) ∪ N ⊆ insert p S - insert p S := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hzN
    · rcases Finset.mem_union.mp hz with hzD | hzP
      · exact Finset.sub_subset_sub (Finset.subset_insert _ _) (Finset.subset_insert _ _) hzD
      · exact newPositiveDifferences_mem h ht hzP
    · have hn := neg_mem_difference (newPositiveDifferences_mem h ht (hNP z hzN))
      simpa only [neg_neg] using hn
  have hNcard : N.card = P.card := Finset.card_image_of_injective _ (by
    intro x y he
    change -x = -y at he
    omega)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hUN, Finset.card_union_of_disjoint hDP, hNcard] at hcard
  have hPcard := newPositiveDifferences_card h ht
  change (P.card : ℤ) = m - 1 at hPcard
  change (D.card : ℤ) + 2 * m - 2 ≤ (insert p S - insert p S).card
  omega

private theorem even_card_bound {m d k t : ℤ} (h : Conditions m d k) (ht : 0 ≤ t) :
    let S := insert m (core m d k t)
    let p := (k + t + 2) * m - d
    ((insert p S + insert p S).card : ℤ) ≤ (insert p S - insert p S).card - m + 3 := by
  intro S p
  have hsum := even_add_card h ht
  have hdiff := even_sub_card h ht
  have hodd := odd_card h ht
  change ((insert p S + insert p S).card : ℤ) ≤ (S + S).card + m at hsum
  change (S - S).card + 2 * m - 2 ≤ ((insert p S - insert p S).card : ℤ) at hdiff
  change (S + S).card = (S - S).card + 1 at hodd
  omega

private theorem strict_insertions {m d k t : ℤ} (h : Conditions m d k) (ht : 0 ≤ t) :
    let S := insert m (core m d k t)
    let p := (k + t + 2) * m - d
    S ⊂ insert p S ∧ insert p S ⊂ insert (-(t + 1) * m - d) (insert p S) := by
  intro S p
  have hm := h.hm
  have hp : p ∉ S := by
    intro hp
    have hb := odd_bounds h ht hp
    dsimp only [p] at *
    nlinarith
  have hl : -(t + 1) * m - d ∉ insert p S := by
    intro hl
    rcases Finset.mem_insert.mp hl with hl | hl
    · have hd := h.hd
      have hdm := h.hdm
      have hk := h.k_ge_three
      dsimp only [p] at hl
      nlinarith
    · have hb := odd_bounds h ht hl
      nlinarith
  exact ⟨(Finset.ssubset_iff_of_subset (Finset.subset_insert _ _)).mpr ⟨p, by simp, hp⟩,
    (Finset.ssubset_iff_of_subset (Finset.subset_insert _ _)).mpr
      ⟨-(t + 1) * m - d, by simp, hl⟩⟩

private theorem core_step (m d k t : ℤ) (hk : -t ≤ k + t + 1) :
    core m d k (t + 1) =
      insert (-(t + 1) * m - d) (insert ((k + t + 2) * m - d) (core m d k t)) := by
  ext z
  constructor
  · intro hz
    rcases (mem_core _ _ _ _ _).mp hz with hb | ⟨j, hj, hjk, rfl⟩ | ⟨b, hb, rfl⟩
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (block_mem_core hb))))
    · by_cases he : j = -(t + 1)
      · subst j
        simp
      by_cases he' : j = k + t + 2
      · subst j
        simp
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr
          (spine_mem_core (by omega) (by omega)))))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (reflected_mem_core hb))))
  · intro hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · subst z
      exact spine_mem_core (by omega) (by omega)
    · rcases Finset.mem_insert.mp hz with hz | hz
      · subst z
        exact spine_mem_core (by omega) (by omega)
      · rcases (mem_core _ _ _ _ _).mp hz with hb | ⟨j, hj, hjk, rfl⟩ | ⟨b, hb, rfl⟩
        · exact block_mem_core hb
        · exact spine_mem_core (by omega) (by omega)
        · exact reflected_mem_core hb

private theorem core_initial (m d k : ℤ) (hk : 1 ≤ k) :
    core m d k 0 = insert (-d) (insert ((k + 1) * m - d)
      (block m d ∪ (Finset.Icc 1 k).image (fun j => j * m - d) ∪
        (block m d).image (fun b => (k + 1) * m - 2 * d - b))) := by
  simpa [core, block, add_assoc] using core_step m d k (-1) (by omega)

private theorem odd_closed (m d k : ℤ) (hk : 1 ≤ k) (A : ℕ → Finset ℤ)
    (h1 : A 1 = insert m (core m d k 0))
    (hodd : ∀ r ≥ 1, A (2 * r + 1) =
      insert (-(r : ℤ) * m - d) (insert ((k + r + 1) * m - d) (A (2 * r - 1)))) :
    ∀ t : ℕ, A (2 * t + 1) = insert m (core m d k t) := by
  intro t
  induction t with
  | zero => simpa using h1
  | succ t ih =>
    have he := hodd (t + 1) (by omega)
    rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega, ih] at he
    rw [show (t.succ : ℤ) = (t : ℤ) + 1 by omega,
      core_step m d k (t : ℤ) (by omega)]
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc,
      show (1 + 1 : ℤ) = 2 by omega, Finset.insert_comm] using he

@[expose] public section

/-- **Alternating sum- and difference-dominated sets from Nathanson's construction.** For a set
$S$ of integers write $S + S = \{s + s' : s, s' \in S\}$, $S - S = \{s - s' : s, s' \in S\}$,
$c + S = \{c + s : s \in S\}$ and $c - S = \{c - s : s \in S\}$. Let $m$, $d$, $k$ be integers with
$m \ge 4$, $m \equiv 0 \pmod 4$ and $4d = m$ or $4d = 3m$, and suppose $k \ge 3$ if $2d < m$ and
$k \ge 4$ if $2d > m$. Let $B = \{0, 1, \dots, m - 1\} \setminus \{d\}$,
$L = \{jm - d : 1 \le j \le k\}$ and $A^* = B \cup L \cup \{(k + 1)m - 2d - b : b \in B\}$. Let
$A_1, A_2, A_3, \dots$ be finite sets of integers with $A_1 = A^* \cup \{m, -d, (k + 1)m - d\}$
and, for every $r \ge 1$, $A_{2r} = A_{2r-1} \cup \{(k + r + 1)m - d\}$ and
$A_{2r+1} = A_{2r-1} \cup \{-rm - d, (k + r + 1)m - d\}$. Then $|A_1 - A_1| < |A_1 + A_1|$, and
for every $r \ge 1$, writing $A'_{2r-1} = A_{2r-1} \setminus \{m\}$: we have
$|A_{2r} + A_{2r}| < |A_{2r} - A_{2r}|$ and $|A_{2r+1} - A_{2r+1}| < |A_{2r+1} + A_{2r+1}|$;
$A_{2r-1} \subsetneq A_{2r} \subsetneq A_{2r+1}$; $m + A'_{2r-1} \subseteq A'_{2r-1} + A'_{2r-1}$
and $m - A'_{2r-1} \subseteq A'_{2r-1} - A'_{2r-1}$;
$|A_{2r-1} + A_{2r-1}| = |A_{2r-1} - A_{2r-1}| + 1$; and
$|A_{2r} + A_{2r}| \le |A_{2r} - A_{2r}| - m + 3$.

Source: Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller and
Steven Senger, *Additional Constructions of Sequences of Alternating Sum and Difference
Dominated Sets*, INTEGERS 26 (2026), Article A88, Theorem 3 (`integers-2026-A88-thm-3`). -/
public theorem alternating_sequence_from_nathanson {m d k : ℤ} (hm : 4 ≤ m)
    (hm4 : m % 4 = 0) (hd : 4 * d = m ∨ 4 * d = 3 * m) (hk3 : 2 * d < m → 3 ≤ k)
    (hk4 : m < 2 * d → 4 ≤ k) (A : ℕ → Finset ℤ)
    (h1 : A 1 = insert (-d) (insert ((k + 1) * m - d) (insert m
      ((Finset.Icc 0 (m - 1)).erase d ∪ (Finset.Icc 1 k).image (fun j => j * m - d) ∪
        ((Finset.Icc 0 (m - 1)).erase d).image (fun b => (k + 1) * m - 2 * d - b)))))
    (heven : ∀ r ≥ 1, A (2 * r) = insert ((k + r + 1) * m - d) (A (2 * r - 1)))
    (hodd : ∀ r ≥ 1, A (2 * r + 1) =
      insert (-(r : ℤ) * m - d) (insert ((k + r + 1) * m - d) (A (2 * r - 1)))) :
    (A 1 - A 1).card < (A 1 + A 1).card ∧
    ∀ r ≥ 1, (A (2 * r) + A (2 * r)).card < (A (2 * r) - A (2 * r)).card ∧
      (A (2 * r + 1) - A (2 * r + 1)).card < (A (2 * r + 1) + A (2 * r + 1)).card ∧
      A (2 * r - 1) ⊂ A (2 * r) ∧ A (2 * r) ⊂ A (2 * r + 1) ∧
      {m} + (A (2 * r - 1)).erase m ⊆ (A (2 * r - 1)).erase m + (A (2 * r - 1)).erase m ∧
      {m} - (A (2 * r - 1)).erase m ⊆ (A (2 * r - 1)).erase m - (A (2 * r - 1)).erase m ∧
      (A (2 * r - 1) + A (2 * r - 1)).card = (A (2 * r - 1) - A (2 * r - 1)).card + 1 ∧
      ((A (2 * r) + A (2 * r)).card : ℤ) ≤ (A (2 * r) - A (2 * r)).card - m + 3 := by
  have h := conditions hm hm4 hd hk3 hk4
  have hk := h.k_ge_three
  have hInit : A 1 = insert m (core m d k 0) := by
    rw [core_initial m d k (by omega)]
    simpa only [block, Finset.insert_comm] using h1
  have hc := odd_closed m d k (by omega) A hInit hodd
  constructor
  · have ho := odd_card (t := 0) h (by omega)
    rw [hInit]
    omega
  · intro r hr
    let t : ℤ := (r - 1 : ℕ)
    have ht : 0 ≤ t := by omega
    have hcast : (r : ℤ) = t + 1 := by dsimp only [t]; omega
    have ho : A (2 * r - 1) = insert m (core m d k t) := by
      rw [show 2 * r - 1 = 2 * (r - 1) + 1 by omega]
      exact hc (r - 1)
    have he : A (2 * r) = insert ((k + t + 2) * m - d) (insert m (core m d k t)) := by
      have he := heven r hr
      rw [ho] at he
      simpa only [hcast, add_assoc, show (1 + 1 : ℤ) = 2 by omega] using he
    have hn : A (2 * r + 1) = insert m (core m d k (t + 1)) := by
      have hn := hodd r hr
      rw [ho] at hn
      rw [core_step m d k t (by omega)]
      simpa only [hcast, add_assoc, show (1 + 1 : ℤ) = 2 by omega,
        Finset.insert_comm] using hn
    have hbound := even_card_bound h ht
    have hstrict := strict_insertions h ht
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [he]
      omega
    · rw [hn]
      have hcard := odd_card h (show 0 ≤ t + 1 by omega)
      omega
    · rw [ho, he]
      exact hstrict.1
    · rw [he, hn, core_step m d k t (by omega)]
      simpa only [Finset.insert_comm] using hstrict.2
    · rw [ho, Finset.erase_insert (m_notMem_core h)]
      exact add_core_subset h ht
    · rw [ho, Finset.erase_insert (m_notMem_core h)]
      exact sub_core_subset h ht
    · rw [ho]
      exact odd_card h ht
    · rw [he]
      exact hbound

end

end MetaMathlibExt
