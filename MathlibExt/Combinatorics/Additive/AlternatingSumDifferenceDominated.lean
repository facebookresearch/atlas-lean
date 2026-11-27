/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Alternating sum- and difference-dominated sets

The shifted-copy construction counts sum and difference levels in each residue class,
then counts the new sums and differences when a single endpoint is adjoined.

## References

* Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller, and Steven Senger,
  *Additional Constructions of Sequences of Alternating Sum and Difference Dominated Sets*,
  INTEGERS 26 (2026), Article A88, Theorems 1 and 3.
* Greg Martin and Kevin O’Bryant, *Many sets have more sums than differences*, in
  *Additive Combinatorics*, CRM Proceedings & Lecture Notes 43, American Mathematical Society
  (2007), 287–305, cited for the two-copy step in Theorem 1.
* Melvyn B. Nathanson, *Sets with More Sums than Differences*, INTEGERS 7 (2007),
  Article A05, pp. 1–24, Theorem 1 (the starting family for Theorem 3).
-/

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

section ShiftedCopies

open Finset

private def shiftBand (S : Finset ℤ) (n u v : ℤ) : Finset ℤ :=
  S + (Icc u v).image (· * n)

private theorem mem_shiftBand {S : Finset ℤ} {n u v z : ℤ} :
    z ∈ shiftBand S n u v ↔ ∃ a ∈ S, ∃ j : ℤ, u ≤ j ∧ j ≤ v ∧ a + j * n = z := by
  simp only [shiftBand, Finset.mem_add, mem_image, mem_Icc]
  constructor
  · rintro ⟨a, ha, _, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨a, ha, j, hj.1, hj.2, rfl⟩
  · rintro ⟨a, ha, j, hj, hj', rfl⟩
    exact ⟨a, ha, j * n, ⟨j, ⟨hj, hj'⟩, rfl⟩, rfl⟩

private theorem int_Icc_add_Icc (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d) :
    Icc a b + Icc c d = Icc (a + c) (b + d) := by
  ext z
  simp only [Finset.mem_add, mem_Icc]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    omega
  · intro hz
    let x := max a (z - d)
    have hx₁ : a ≤ x := le_max_left _ _
    have hx₂ : x ≤ b := max_le hab (by omega)
    have hx₃ : z - d ≤ x := le_max_right _ _
    have hx₄ : x ≤ z - c := max_le (by omega) (by omega)
    exact ⟨x, ⟨hx₁, hx₂⟩, z - x, ⟨by omega, by omega⟩, by omega⟩

private def levels (S : Finset ℤ) (n r : ℤ) : Finset ℤ :=
  (S.filter (fun z ↦ z % n = r)).image (· / n)

private theorem mem_levels {S : Finset ℤ} {n r q : ℤ} :
    q ∈ levels S n r ↔ ∃ z ∈ S, z % n = r ∧ z / n = q := by
  simp only [levels, mem_image, mem_filter, and_assoc]

private theorem levels_card (S : Finset ℤ) (n r : ℤ) :
    (levels S n r).card = (S.filter (fun z ↦ z % n = r)).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy h
  have hx' := (mem_filter.mp hx).2
  have hy' := (mem_filter.mp hy).2
  change x / n = y / n at h
  have ex := Int.emod_add_mul_ediv x n
  have ey := Int.emod_add_mul_ediv y n
  rw [h, hx'] at ex
  rw [hy'] at ey
  omega

private theorem levels_shiftBand (S : Finset ℤ) {n : ℤ} (hn : 0 < n) (u v r : ℤ) :
    levels (shiftBand S n u v) n r = levels S n r + Icc u v := by
  have hmod (a j : ℤ) : (a + j * n) % n = a % n := by simp
  have hdiv (a j : ℤ) : (a + j * n) / n = a / n + j := Int.add_mul_ediv_right a j hn.ne'
  ext q
  simp only [mem_levels, mem_shiftBand, Finset.mem_add, mem_Icc]
  constructor
  · rintro ⟨_, ⟨a, ha, j, hj, hj', rfl⟩, h₁, h₂⟩
    exact ⟨a / n, ⟨a, ha, (hmod a j).symm.trans h₁, rfl⟩, j, ⟨hj, hj'⟩,
      (hdiv a j).symm.trans h₂⟩
  · rintro ⟨_, ⟨a, ha, h₁, rfl⟩, j, ⟨hj, hj'⟩, rfl⟩
    exact ⟨a + j * n, ⟨a, ha, j, hj, hj', rfl⟩, (hmod a j).trans h₁, hdiv a j⟩

private theorem residues_shiftBand (S : Finset ℤ) {n u v : ℤ} (huv : u ≤ v) :
    (shiftBand S n u v).image (· % n) = S.image (· % n) := by
  ext r
  simp only [mem_image, mem_shiftBand]
  constructor
  · rintro ⟨_, ⟨a, ha, j, _, _, rfl⟩, rfl⟩
    exact ⟨a, ha, by simp⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a + u * n, ⟨a, ha, u, le_rfl, huv, rfl⟩, by simp⟩

-- A nonempty residue class in two bands is an interval of one or two levels.
private theorem levels_eq_Icc {S : Finset ℤ} {n L r : ℤ} (hn : 0 < n)
    (hS : ∀ a ∈ S, L * n ≤ a ∧ a < (L + 2) * n) (hr : r ∈ S.image (· % n)) :
    ∃ a b : ℤ, a ≤ b ∧ levels S n r = Icc a b := by
  have bounds (q : ℤ) (hq : q ∈ levels S n r) : L ≤ q ∧ q ≤ L + 1 := by
    obtain ⟨z, hz, _, rfl⟩ := mem_levels.mp hq
    have hl := (Int.le_ediv_iff_mul_le hn).mpr (hS z hz).1
    have hu := (Int.ediv_lt_iff_lt_mul hn).mpr (hS z hz).2
    omega
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hr
  let C := levels S n (z % n)
  have hC : C.Nonempty := ⟨z / n, mem_levels.mpr ⟨z, hz, rfl, rfl⟩⟩
  let a := C.min' hC
  let b := C.max' hC
  have ha : a ∈ C := C.min'_mem hC
  have hb : b ∈ C := C.max'_mem hC
  refine ⟨a, b, C.min'_le b hb, ?_⟩
  change C = Icc a b
  ext q
  rw [mem_Icc]
  refine ⟨fun hq ↦ ⟨C.min'_le q hq, C.le_max' q hq⟩, fun hq ↦ ?_⟩
  have h₁ := (bounds a ha).1
  have h₂ := (bounds b hb).2
  have h : q = a ∨ q = b := by omega
  rcases h with rfl | rfl <;> assumption

-- Each occupied residue class grows by the length of the shift interval minus one.
private theorem shiftBand_card {S : Finset ℤ} {n L u v : ℤ} (hn : 0 < n) (huv : u ≤ v)
    (hS : ∀ a ∈ S, L * n ≤ a ∧ a < (L + 2) * n) :
    (shiftBand S n u v).card = S.card + (S.image (· % n)).card * (v - u).toNat := by
  conv_lhs => rw [Finset.card_eq_sum_card_image (· % n)]
  conv_rhs => lhs; rw [Finset.card_eq_sum_card_image (· % n)]
  have hconst : (∑ _r ∈ S.image (· % n), (v - u).toNat) =
      (S.image (· % n)).card * (v - u).toNat := Finset.sum_const_nat (fun _ _ ↦ rfl)
  rw [residues_shiftBand S huv, ← hconst, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  rw [← levels_card, ← levels_card, levels_shiftBand S hn]
  obtain ⟨a, b, hab, hC⟩ := levels_eq_Icc hn hS hr
  rw [hC, int_Icc_add_Icc _ _ _ _ hab huv, Int.card_Icc, Int.card_Icc]
  omega

-- Indices of translated copies add in `[0, 2t]` and subtract in `[-t, t]`.
private theorem copy_add (S : Finset ℤ) (n t : ℤ) (ht : 0 ≤ t) :
    shiftBand S n 0 t + shiftBand S n 0 t = shiftBand (S + S) n 0 (2 * t) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨a, ha, i, hi, hi', rfl⟩ := mem_shiftBand.mp hx
    obtain ⟨b, hb, j, hj, hj', rfl⟩ := mem_shiftBand.mp hy
    exact mem_shiftBand.mpr ⟨a + b, Finset.add_mem_add ha hb, i + j, by omega, by omega, by ring⟩
  · intro hz
    obtain ⟨x, hx, q, hq, hq', rfl⟩ := mem_shiftBand.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
    let i := min q t
    have hi : 0 ≤ i := le_min hq ht
    have hi' : i ≤ t := min_le_right _ _
    have hj : 0 ≤ q - i := sub_nonneg.mpr (min_le_left _ _)
    have hj' : q - i ≤ t := by dsimp [i]; omega
    exact Finset.mem_add.mpr ⟨a + i * n, mem_shiftBand.mpr ⟨a, ha, i, hi, hi', rfl⟩,
      b + (q - i) * n, mem_shiftBand.mpr ⟨b, hb, q - i, hj, hj', rfl⟩, by ring⟩

private theorem copy_sub (S : Finset ℤ) (n t : ℤ) :
    shiftBand S n 0 t - shiftBand S n 0 t = shiftBand (S - S) n (-t) t := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp hz
    obtain ⟨a, ha, i, hi, hi', rfl⟩ := mem_shiftBand.mp hx
    obtain ⟨b, hb, j, hj, hj', rfl⟩ := mem_shiftBand.mp hy
    exact mem_shiftBand.mpr ⟨a - b, Finset.sub_mem_sub ha hb, i - j, by omega, by omega, by ring⟩
  · intro hz
    obtain ⟨x, hx, q, hq, hq', rfl⟩ := mem_shiftBand.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
    let i := max q 0
    let j := max (-q) 0
    have hi : 0 ≤ i := le_max_right _ _
    have hi' : i ≤ t := max_le hq' (by omega)
    have hj : 0 ≤ j := le_max_right _ _
    have hj' : j ≤ t := max_le (by omega) (by omega)
    have hqij : i - j = q := by dsimp [i, j]; omega
    rw [← hqij]
    exact Finset.mem_sub.mpr ⟨a + i * n, mem_shiftBand.mpr ⟨a, ha, i, hi, hi', rfl⟩,
      b + j * n, mem_shiftBand.mpr ⟨b, hb, j, hj, hj', rfl⟩, by ring⟩

private theorem base_add_bounds {S : Finset ℤ} {n : ℤ} (hS : ∀ a ∈ S, 0 ≤ a ∧ a < n)
    {x : ℤ} (hx : x ∈ S + S) : 0 ≤ x ∧ x < 2 * n := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
  have := hS a ha
  have := hS b hb
  omega

private theorem base_sub_bounds {S : Finset ℤ} {n : ℤ} (hS : ∀ a ∈ S, 0 ≤ a ∧ a < n)
    {x : ℤ} (hx : x ∈ S - S) : -n < x ∧ x < n := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
  have := hS a ha
  have := hS b hb
  omega

private theorem copy_card_bias {S : Finset ℤ} {n t : ℤ} (hn : 0 < n) (ht : 0 ≤ t)
    (hS : ∀ a ∈ S, 0 ≤ a ∧ a < n)
    (hmod : ((S + S).image (· % n)).card = ((S - S).image (· % n)).card) :
    let C := shiftBand S n 0 t
    ((C + C).card : ℤ) - (C - C).card = ((S + S).card : ℤ) - (S - S).card := by
  have hs := shiftBand_card (L := 0) (u := 0) (v := 2 * t) hn (by omega)
    (fun a ha ↦ by simpa using base_add_bounds hS ha)
  have hd := shiftBand_card (L := -1) (u := -t) (v := t) hn (by omega)
    (fun a ha ↦ by simpa using (show -n ≤ a ∧ a < n from
      ⟨(base_sub_bounds hS ha).1.le, (base_sub_bounds hS ha).2⟩))
  rw [hmod, show 2 * t - 0 = t - -t by omega] at hs
  dsimp only
  rw [copy_add S n t ht, copy_sub S n t, hs, hd]
  omega

-- An element in the top band can only come from the last shift.
private theorem mem_shiftBand_top {S : Finset ℤ} {n u v b z : ℤ} (hn : 0 < n) (huv : u ≤ v)
    (hS : ∀ a ∈ S, a < b + n) (hz : v * n + b ≤ z) :
    z ∈ shiftBand S n u v ↔ z - v * n ∈ S := by
  constructor
  · intro h
    obtain ⟨a, ha, j, hj, hj', he⟩ := mem_shiftBand.mp h
    have htop : j = v := by
      by_contra hne
      have hm := mul_le_mul_of_nonneg_right (show j + 1 ≤ v by omega) hn.le
      rw [add_mul, one_mul] at hm
      have := hS a ha
      omega
    subst j
    rwa [show z - v * n = a by omega]
  · intro h
    exact mem_shiftBand.mpr ⟨z - v * n, h, v, huv, le_rfl, by omega⟩

private theorem mem_copy_lt_endpoint {S : Finset ℤ} {n t a : ℤ} (hn : 0 < n)
    (hS : ∀ a ∈ S, 0 ≤ a ∧ a < n) (ha : a ∈ shiftBand S n 0 t) : a < (t + 1) * n := by
  obtain ⟨b, hb, j, _, hj, rfl⟩ := mem_shiftBand.mp ha
  have hm := mul_le_mul_of_nonneg_right hj hn.le
  rw [add_mul, one_mul]
  have := (hS b hb).2
  omega

-- Before the last shift, the extra sum is already present because `0 ∈ S`.
private theorem endpoint_sum_fresh {S : Finset ℤ} {n t a j : ℤ} (hn : 0 < n)
    (h0 : 0 ∈ S) (hS : ∀ a ∈ S, 0 ≤ a ∧ a < n) (ha : a ∈ S) (hj : 0 ≤ j) (hj' : j ≤ t) :
    (t + 1) * n + (a + j * n) ∉ shiftBand S n 0 t + shiftBand S n 0 t ↔
      j = t ∧ n + a ∉ S + S := by
  have ht : 0 ≤ t := hj.trans hj'
  rw [copy_add S n t ht]
  by_cases h : j = t
  · subst j
    have hz : 2 * t * n + n ≤ (t + 1) * n + (a + t * n) := by
      rw [show (t + 1) * n + (a + t * n) = 2 * t * n + n + a by ring]
      exact le_add_of_nonneg_right (hS a ha).1
    rw [mem_shiftBand_top hn (by omega) (fun _ hx ↦ by
      have := (base_add_bounds hS hx).2
      omega) hz, show (t + 1) * n + (a + t * n) - 2 * t * n = n + a by ring]
    simp
  · have hm : (t + 1) * n + (a + j * n) ∈ shiftBand (S + S) n 0 (2 * t) :=
      mem_shiftBand.mpr ⟨a, by simpa using Finset.add_mem_add h0 ha, t + 1 + j,
        by omega, by omega, by ring⟩
    simp [h, hm]

-- Before the last difference level, the extra difference is already present as `0 - a`.
private theorem endpoint_sub_fresh {S : Finset ℤ} {n t a j : ℤ} (hn : 0 < n)
    (h0 : 0 ∈ S) (hS : ∀ a ∈ S, 0 ≤ a ∧ a < n) (ha : a ∈ S) (hj : 0 ≤ j) (hj' : j ≤ t) :
    (t + 1) * n - (a + j * n) ∉ shiftBand S n 0 t - shiftBand S n 0 t ↔
      j = 0 ∧ n - a ∉ S - S := by
  have ht : 0 ≤ t := hj.trans hj'
  rw [copy_sub S n t]
  by_cases h : j = 0
  · subst j
    have hz : t * n + 0 ≤ (t + 1) * n - (a + 0 * n) := by
      rw [show (t + 1) * n - (a + 0 * n) = t * n + (n - a) by ring]
      simpa using (show 0 ≤ n - a by have := (hS a ha).2; omega)
    rw [mem_shiftBand_top hn (by omega) (fun _ hx ↦ by
      simpa using (base_sub_bounds hS hx).2) hz,
      show (t + 1) * n - (a + 0 * n) - t * n = n - a by ring]
    simp
  · have hm : (t + 1) * n - (a + j * n) ∈ shiftBand (S - S) n (-t) t :=
      mem_shiftBand.mpr ⟨0 - a, Finset.sub_mem_sub h0 ha, t + 1 - j, by omega, by omega, by ring⟩
    simp [h, hm]

private theorem copy_endpoint_filters {S : Finset ℤ} {n t : ℤ} (hn : 0 < n) (ht : 0 ≤ t)
    (h0 : 0 ∈ S) (hS : ∀ a ∈ S, 0 ≤ a ∧ a < n) :
    let C := shiftBand S n 0 t
    let p := (t + 1) * n
    (C.filter (fun a ↦ p + a ∉ C + C)).card = (S.filter (fun a ↦ n + a ∉ S + S)).card ∧
    (C.filter (fun a ↦ p - a ∉ C - C)).card = (S.filter (fun a ↦ n - a ∉ S - S)).card := by
  intro C p
  constructor
  · have he : C.filter (fun a ↦ p + a ∉ C + C) =
        (S.filter (fun a ↦ n + a ∉ S + S)).image (fun a ↦ a + t * n) := by
      ext a
      constructor
      · intro ha
        obtain ⟨ha, hf⟩ := mem_filter.mp ha
        obtain ⟨b, hb, j, hj, hj', rfl⟩ := mem_shiftBand.mp ha
        obtain ⟨rfl, h⟩ := (endpoint_sum_fresh hn h0 hS hb hj hj').mp hf
        exact mem_image.mpr ⟨b, mem_filter.mpr ⟨hb, h⟩, rfl⟩
      · intro ha
        obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
        obtain ⟨hb, hf⟩ := mem_filter.mp hb
        exact mem_filter.mpr ⟨mem_shiftBand.mpr ⟨b, hb, t, ht, le_rfl, rfl⟩,
          (endpoint_sum_fresh hn h0 hS hb ht le_rfl).mpr ⟨rfl, hf⟩⟩
    rw [he, card_image_of_injective _ (fun x y (h : x + t * n = y + t * n) ↦ by omega)]
  · congr 1
    ext a
    constructor
    · intro ha
      obtain ⟨ha, hf⟩ := mem_filter.mp ha
      obtain ⟨b, hb, j, hj, hj', rfl⟩ := mem_shiftBand.mp ha
      obtain ⟨rfl, h⟩ := (endpoint_sub_fresh hn h0 hS hb hj hj').mp hf
      simpa using (mem_filter.mpr ⟨hb, h⟩ : b ∈ S.filter (fun x ↦ n - x ∉ S - S))
    · intro ha
      obtain ⟨ha, hf⟩ := mem_filter.mp ha
      have h := (endpoint_sub_fresh (j := 0) hn h0 hS ha le_rfl ht).mpr ⟨rfl, hf⟩
      exact mem_filter.mpr ⟨mem_shiftBand.mpr ⟨a, ha, 0, le_rfl, ht, by simp⟩, by simpa using h⟩

-- Count the sums from adjoining a point strictly above the set.
private theorem insert_endpoint_add_card (C : Finset ℤ) (p : ℤ) (hC : ∀ a ∈ C, a < p) :
    (insert p C + insert p C).card =
      (C + C).card + (C.filter (fun a ↦ p + a ∉ C + C)).card + 1 := by
  let P := (C.filter (fun a ↦ p + a ∉ C + C)).image (p + ·)
  have hP : p + p ∉ P := by
    intro hz
    obtain ⟨a, ha, he⟩ := mem_image.mp hz
    have := hC a (mem_filter.mp ha).1
    omega
  have hp : p + p ∉ C + C := by
    intro hz
    obtain ⟨a, ha, b, hb, he⟩ := Finset.mem_add.mp hz
    have := hC a ha
    have := hC b hb
    omega
  have hnew : (insert p C + insert p C) \ (C + C) = insert (p + p) P := by
    ext z
    constructor
    · intro hz
      obtain ⟨hz, hf⟩ := mem_sdiff.mp hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
      rcases mem_insert.mp ha with hap | ha <;> rcases mem_insert.mp hb with hbp | hb
      · subst a b
        exact mem_insert_self _ _
      · subst a
        exact mem_insert_of_mem (mem_image.mpr ⟨b, mem_filter.mpr ⟨hb, hf⟩, rfl⟩)
      · subst b
        have hf' : p + a ∉ C + C := by simpa only [add_comm] using hf
        exact mem_insert_of_mem (mem_image.mpr ⟨a, mem_filter.mpr ⟨ha, hf'⟩, add_comm _ _⟩)
      · exact (hf (Finset.add_mem_add ha hb)).elim
    · intro hz
      rcases mem_insert.mp hz with rfl | hz
      · exact mem_sdiff.mpr ⟨Finset.add_mem_add (mem_insert_self _ _) (mem_insert_self _ _), hp⟩
      · obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
        obtain ⟨ha, hf⟩ := mem_filter.mp ha
        exact mem_sdiff.mpr ⟨Finset.add_mem_add (mem_insert_self _ _) (mem_insert_of_mem ha), hf⟩
  have hc := card_sdiff_add_card_eq_card
    (Finset.add_subset_add (subset_insert p C) (subset_insert p C))
  rw [hnew, card_insert_of_notMem hP] at hc
  have hcard : P.card = (C.filter (fun a ↦ p + a ∉ C + C)).card :=
    card_image_of_injective _ (fun x y (h : p + x = p + y) ↦ by omega)
  omega

-- The new differences are the positive ones from the endpoint and their negatives.
private theorem insert_endpoint_sub_card (C : Finset ℤ) (p : ℤ) (hC : ∀ a ∈ C, a < p)
    (hne : C.Nonempty) :
    (insert p C - insert p C).card =
      (C - C).card + 2 * (C.filter (fun a ↦ p - a ∉ C - C)).card := by
  let P := (C.filter (fun a ↦ p - a ∉ C - C)).image (p - ·)
  let N := P.image (fun a ↦ -a)
  have hP (z : ℤ) : z ∈ P ↔ ∃ a ∈ C, p - a ∉ C - C ∧ p - a = z := by
    simp only [P, mem_image, mem_filter, and_assoc]
  have hpos (z : ℤ) (hz : z ∈ P) : 0 < z := by
    obtain ⟨a, ha, _, rfl⟩ := (hP z).mp hz
    exact sub_pos.mpr (hC a ha)
  have hN (z : ℤ) : z ∈ N ↔ -z ∈ P := by simp [N, mem_image, neg_eq_iff_eq_neg]
  have hdis : Disjoint P N := disjoint_left.mpr (fun z hp hn ↦ by
    have := hpos z hp
    have := hpos (-z) ((hN z).mp hn)
    omega)
  have hnew : (insert p C - insert p C) \ (C - C) = P ∪ N := by
    ext z
    constructor
    · intro hz
      obtain ⟨hz, hf⟩ := mem_sdiff.mp hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
      rcases mem_insert.mp ha with hap | ha <;> rcases mem_insert.mp hb with hbp | hb
      · subst a b
        obtain ⟨c, hc⟩ := hne
        exact (hf (Finset.mem_sub.mpr ⟨c, hc, c, hc, by omega⟩)).elim
      · subst a
        exact mem_union_left _ ((hP _).mpr ⟨b, hb, hf, rfl⟩)
      · subst b
        have hf' : p - a ∉ C - C := fun h ↦ hf (by
          simpa only [neg_sub] using neg_mem_difference h)
        exact mem_union_right _ ((hN _).mpr ((hP _).mpr ⟨a, ha, hf', by omega⟩))
      · exact (hf (Finset.sub_mem_sub ha hb)).elim
    · intro hz
      rcases mem_union.mp hz with hz | hz
      · obtain ⟨a, ha, hf, rfl⟩ := (hP z).mp hz
        exact mem_sdiff.mpr ⟨Finset.sub_mem_sub (mem_insert_self _ _) (mem_insert_of_mem ha), hf⟩
      · obtain ⟨a, ha, hf, he⟩ := (hP (-z)).mp ((hN z).mp hz)
        have hz : z = a - p := by omega
        subst z
        exact mem_sdiff.mpr ⟨Finset.sub_mem_sub (mem_insert_of_mem ha) (mem_insert_self _ _),
          fun h ↦ hf (by simpa only [neg_sub] using neg_mem_difference h)⟩
  have hc := card_sdiff_add_card_eq_card
    (Finset.sub_subset_sub (subset_insert p C) (subset_insert p C))
  have hcard : P.card = (C.filter (fun a ↦ p - a ∉ C - C)).card :=
    card_image_of_injective _ (fun x y (h : p - x = p - y) ↦ by omega)
  have hncard : N.card = P.card := card_image_of_injective _ (fun x y (h : -x = -y) ↦ by omega)
  rw [hnew, card_union_of_disjoint hdis, hncard, hcard] at hc
  omega

private theorem odd_copies (S : Finset ℤ) (n : ℤ) (A : ℕ → Finset ℤ) (h1 : A 1 = S)
    (hodd : ∀ l ≥ 1, A (2 * l + 1) = A (2 * l - 1) ∪ (S + {(l : ℤ) * n})) :
    ∀ t : ℕ, A (2 * t + 1) = shiftBand S n 0 t := by
  intro t
  induction t with
  | zero =>
    have hB : shiftBand S n 0 0 = S := by
      ext z
      rw [mem_shiftBand]
      constructor
      · rintro ⟨a, ha, j, hj, hj', rfl⟩
        simpa [le_antisymm hj' hj] using ha
      · intro hz
        exact ⟨z, hz, 0, le_rfl, le_rfl, by simp⟩
    simpa [hB] using h1
  | succ t ih =>
    rw [hodd (t + 1) (Nat.succ_pos _), show 2 * (t + 1) - 1 = 2 * t + 1 by omega, ih]
    ext z
    simp only [mem_union, mem_shiftBand, Finset.mem_add, mem_singleton, Nat.cast_succ]
    constructor
    · rintro (⟨a, ha, j, hj, hj', rfl⟩ | ⟨a, ha, _, rfl, rfl⟩)
      · exact ⟨a, ha, j, hj, by omega, rfl⟩
      · exact ⟨a, ha, (t : ℤ) + 1, by omega, le_rfl, rfl⟩
    · rintro ⟨a, ha, j, hj, hj', rfl⟩
      by_cases h : j = (t : ℤ) + 1
      · exact Or.inr ⟨a, ha, j * n, by rw [h], rfl⟩
      · exact Or.inl ⟨a, ha, j, hj, by omega, rfl⟩

end ShiftedCopies

/-- **Alternating sum- and difference-dominated sets from shifted copies.** For a set $S$ of
integers write $S + S = \{s + s' : s, s' \in S\}$ and $S - S = \{s - s' : s, s' \in S\}$. Let $A_1$
be a finite set of integers with $|A_1 - A_1| < |A_1 + A_1|$ and $0 \in A_1$, and let $n$ be an
integer with $0 \le a < n$ for every $a \in A_1$. Suppose that (a) $A_1 + A_1$ and $A_1 - A_1$
meet the same number of residue classes modulo $n$, and (b) with
$x = \#\{a \in A_1 : n + a \notin A_1 + A_1\}$ and $y = \#\{b \in A_1 : n - b \notin A_1 - A_1\}$
we have $2y - x - 1 > |A_1 + A_1| - |A_1 - A_1|$. Let $A_1, A_2, A_3, \dots$ be finite sets of
integers, starting with this $A_1$, such that for every $l \ge 1$, $A_{2l} = A_{2l-1} \cup \{ln\}$
and $A_{2l+1} = A_{2l-1} \cup \{a + ln : a \in A_1\}$. Then for every $l \ge 1$,
$|A_{2l} + A_{2l}| < |A_{2l} - A_{2l}|$, $|A_{2l+1} - A_{2l+1}| < |A_{2l+1} + A_{2l+1}|$ and
$A_{2l-1} \subsetneq A_{2l} \subsetneq A_{2l+1}$.

Source: Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller and
Steven Senger, *Additional Constructions of Sequences of Alternating Sum and Difference
Dominated Sets*, INTEGERS 26 (2026), Article A88, Theorem 1 (`integers-2026-A88-thm-1`). -/
public theorem alternating_sequence_of_copies (A₁ : Finset ℤ) (n : ℤ)
    (hmstd : (A₁ - A₁).card < (A₁ + A₁).card) (h0 : 0 ∈ A₁) (hn : ∀ a ∈ A₁, 0 ≤ a ∧ a < n)
    (hmod : ((A₁ + A₁).image (· % n)).card = ((A₁ - A₁).image (· % n)).card)
    (hxy : 2 * ((A₁.filter fun b => n - b ∉ A₁ - A₁).card : ℤ) -
        (A₁.filter fun a => n + a ∉ A₁ + A₁).card - 1 >
      ((A₁ + A₁).card : ℤ) - (A₁ - A₁).card)
    (A : ℕ → Finset ℤ) (h1 : A 1 = A₁)
    (heven : ∀ l ≥ 1, A (2 * l) = A (2 * l - 1) ∪ {(l : ℤ) * n})
    (hodd : ∀ l ≥ 1, A (2 * l + 1) = A (2 * l - 1) ∪ (A₁ + {(l : ℤ) * n})) :
    ∀ l ≥ 1, (A (2 * l) + A (2 * l)).card < (A (2 * l) - A (2 * l)).card ∧
      (A (2 * l + 1) - A (2 * l + 1)).card < (A (2 * l + 1) + A (2 * l + 1)).card ∧
      A (2 * l - 1) ⊂ A (2 * l) ∧ A (2 * l) ⊂ A (2 * l + 1) := by
  have hn₀ : 0 < n := (hn 0 h0).2
  have hc := odd_copies A₁ n A h1 hodd
  have hnonzero : ∃ a ∈ A₁, 0 < a := by
    by_contra! h
    have hsingle : A₁ = {0} := by
      ext a
      simp only [Finset.mem_singleton]
      constructor
      · intro ha
        have := (hn a ha).1
        have := h a ha
        omega
      · rintro rfl
        exact h0
    simp [hsingle] at hmstd
  intro l hl
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
  have ho : A (2 * (t + 1) - 1) = shiftBand A₁ n 0 t := by
    rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega, hc]
  have he : A (2 * (t + 1)) = insert (((t : ℤ) + 1) * n) (shiftBand A₁ n 0 t) := by
    rw [heven (t + 1) hl, ho, Nat.cast_succ]
    ext z
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_comm]
  have hn' : A (2 * (t + 1) + 1) = shiftBand A₁ n 0 ((t : ℤ) + 1) := by
    simpa only [Nat.cast_succ] using hc (t + 1)
  let C := shiftBand A₁ n 0 t
  let p := ((t : ℤ) + 1) * n
  have hbound (a : ℤ) (ha : a ∈ C) : a < p := mem_copy_lt_endpoint hn₀ hn ha
  have hne : C.Nonempty := ⟨0, mem_shiftBand.mpr ⟨0, h0, 0, le_rfl, by omega, by simp⟩⟩
  have hb := copy_card_bias (t := (t : ℤ)) hn₀ (by omega) hn hmod
  have hb' := copy_card_bias (t := (t : ℤ) + 1) hn₀ (by omega) hn hmod
  have hf := copy_endpoint_filters (t := (t : ℤ)) hn₀ (by omega) h0 hn
  change (C.filter (fun a ↦ p + a ∉ C + C)).card = _ ∧
    (C.filter (fun a ↦ p - a ∉ C - C)).card = _ at hf
  have hsum := insert_endpoint_add_card C p hbound
  have hdiff := insert_endpoint_sub_card C p hbound hne
  rw [hf.1] at hsum
  rw [hf.2] at hdiff
  rw [ho, he, hn']
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (insert p C + insert p C).card < (insert p C - insert p C).card
    change ((C + C).card : ℤ) - (C - C).card = _ at hb
    omega
  · dsimp only at hb'
    omega
  · exact (Finset.ssubset_iff_of_subset (Finset.subset_insert p C)).mpr
      ⟨p, Finset.mem_insert_self _ _, fun hp ↦ (lt_irrefl p) (hbound p hp)⟩
  · apply (Finset.ssubset_iff_of_subset ?_).mpr
    · obtain ⟨a, ha, hpos⟩ := hnonzero
      refine ⟨a + p, mem_shiftBand.mpr ⟨a, ha, (t : ℤ) + 1, by omega, le_rfl, rfl⟩, ?_⟩
      intro hz
      rcases Finset.mem_insert.mp hz with h | h
      · omega
      · have := hbound _ h
        omega
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact mem_shiftBand.mpr ⟨0, h0, (t : ℤ) + 1, by omega, le_rfl, by simp⟩
      · obtain ⟨a, ha, j, hj, hj', rfl⟩ := mem_shiftBand.mp hz
        exact mem_shiftBand.mpr ⟨a, ha, j, hj, by omega, rfl⟩

end MetaMathlibExt
