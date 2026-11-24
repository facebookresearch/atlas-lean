/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fintype.Lattice

/-!
# The Lenstra–Shmoys–Tardos rounding theorem

`exists_assignment_load_le` rounds a fractional assignment on unrelated parallel machines
to a schedule exceeding each machine's deadline by at most the largest allowed processing time.

At each machine, jobs of processing time at least `k` can use only the first
`⌈mass k⌉₊` slots, where `mass k` is their total fractional assignment on that machine.
These nested sets of slots satisfy Hall's condition. Summing the matched job counts over
positive thresholds counts the integral load, with a rounding loss of at most one per threshold.
-/

namespace MathlibExt.ComputerScience.UnrelatedMachinesRoundingWanted

open Finset

section

variable {M J : Type*} [Fintype J]

private def mass (p : M → J → ℕ) (x : M → J → ℝ) (i : M) (k : ℕ) : ℝ :=
  ∑ j with k ≤ p i j, x i j

private theorem mass_antitone (p : M → J → ℕ) (x : M → J → ℝ) (hx : ∀ i j, 0 ≤ x i j)
    (i : M) : Antitone (mass p x i) := by
  intro k l h
  exact sum_le_sum_of_subset_of_nonneg
    (fun j hj => mem_filter.mpr ⟨mem_univ _, h.trans (mem_filter.mp hj).2⟩) fun j _ _ => hx i j

variable [Fintype M]

private noncomputable def slots (p : M → J → ℕ) (x : M → J → ℝ) (j : J) :
    Finset (M × ℕ) := by
  classical
  exact (univ.filter fun i => 0 < x i j).biUnion fun i =>
    {i} ×ˢ range ⌈mass p x i (p i j)⌉₊

private theorem mem_slots (p : M → J → ℕ) (x : M → J → ℝ) (j : J) (v : M × ℕ) :
    v ∈ slots p x j ↔ 0 < x v.1 j ∧ v.2 < ⌈mass p x v.1 (p v.1 j)⌉₊ := by
  classical
  rcases v with ⟨i, n⟩
  simp [slots, Prod.mk.injEq]

-- On a machine, a shortest job in the subset's positive support can use enough slots
-- to accommodate the entire fractional mass of that subset on the machine.
private theorem mass_le_neighbor_card (p : M → J → ℕ) (x : M → J → ℝ)
    (hx : ∀ i j, 0 ≤ x i j) (s : Finset J) (i : M) [DecidableEq M] :
    ∑ j ∈ s, x i j ≤ ((s.biUnion (slots p x)).filter fun v => v.1 = i).card := by
  classical
  let a := s.filter fun j => 0 < x i j
  have hsum : ∑ j ∈ s, x i j = ∑ j ∈ a, x i j := by
    apply Eq.symm
    apply sum_subset (filter_subset _ _)
    intro j hj hja
    exact le_antisymm (le_of_not_gt fun h => hja (mem_filter.mpr ⟨hj, h⟩)) (hx i j)
  rw [hsum]
  by_cases h : a.Nonempty
  · obtain ⟨j, hj, hmin⟩ := a.exists_min_image (p i) h
    obtain ⟨hjs, hjpos⟩ := mem_filter.mp hj
    calc
      ∑ l ∈ a, x i l ≤ mass p x i (p i j) :=
        sum_le_sum_of_subset_of_nonneg
          (fun l hl => mem_filter.mpr ⟨mem_univ _, hmin l hl⟩) fun l _ _ => hx i l
      _ ≤ ⌈mass p x i (p i j)⌉₊ := Nat.le_ceil _
      _ ≤ _ := by
        apply Nat.cast_le.mpr
        rw [← card_range ⌈mass p x i (p i j)⌉₊]
        apply card_le_card_of_injOn (fun n => (i, n)) _ (fun _ _ _ _ e => congrArg Prod.snd e)
        intro n hn
        exact mem_filter.mpr ⟨mem_biUnion.mpr
          ⟨j, hjs, (mem_slots ..).2 ⟨hjpos, mem_range.mp hn⟩⟩, rfl⟩
  · simp [not_nonempty_iff_eq_empty.mp h]

private theorem match_slots (p : M → J → ℕ) (x : M → J → ℝ) (hx : ∀ i j, 0 ≤ x i j)
    (hjob : ∀ j, ∑ i, x i j = 1) :
    ∃ f : J → M × ℕ, Function.Injective f ∧ ∀ j, f j ∈ slots p x j := by
  classical
  apply (all_card_le_biUnion_card_iff_existsInjective' _).mp
  intro s
  suffices (s.card : ℝ) ≤ (s.biUnion (slots p x)).card by exact_mod_cast this
  calc
    (s.card : ℝ) = ∑ j ∈ s, (1 : ℝ) := by simp
    _ = ∑ i, ∑ j ∈ s, x i j := by rw [sum_comm]; simp [hjob]
    _ ≤ ∑ i, (((s.biUnion (slots p x)).filter fun v => v.1 = i).card : ℝ) :=
      sum_le_sum fun i _ => mass_le_neighbor_card p x hx s i
    _ = ((s.biUnion (slots p x)).card : ℝ) := by
      rw [← Nat.cast_sum]
      exact congrArg Nat.cast (by simpa using
        sum_card_fiberwise_eq_card_filter (s.biUnion (slots p x)) univ Prod.fst)

-- Summing the mass above each threshold counts each job once per unit of processing time,
-- up to the truncation at t.
omit [Fintype J] in
private theorem sum_layers (s : Finset J) (p : J → ℕ) (w : J → ℝ) (t : ℕ) :
    ∑ k ∈ range t, ∑ j ∈ s with k < p j, w j = ∑ j ∈ s, (min t (p j) : ℕ) * w j := by
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [← sum_filter]
  have h : (range t).filter (· < p j) = range (min t (p j)) := by ext; simp [lt_min_iff]
  simp [h]

private theorem count_layer_le (p : M → J → ℕ) (x : M → J → ℝ) (hx : ∀ i j, 0 ≤ x i j)
    (f : J → M × ℕ) (hf : Function.Injective f) (hslots : ∀ j, f j ∈ slots p x j)
    [DecidableEq M] (i : M) (k : ℕ) :
    ((univ.filter fun j => (f j).1 = i).filter fun j => k < p i j).card ≤
      ⌈mass p x i (k + 1)⌉₊ := by
  classical
  rw [← card_range ⌈mass p x i (k + 1)⌉₊]
  apply card_le_card_of_injOn (fun j => (f j).2)
  · intro j hj
    obtain ⟨hi, hlt⟩ := mem_filter.mp hj
    have he := (mem_filter.mp hi).2
    have hslot := ((mem_slots ..).1 (hslots j)).2
    rw [he] at hslot
    exact mem_range.mpr (hslot.trans_le (Nat.ceil_le_ceil (mass_antitone p x hx i hlt)))
  · intro j hj l hl he
    apply hf (Prod.ext _ he)
    exact (mem_filter.mp (mem_filter.mp hj).1).2.trans (mem_filter.mp (mem_filter.mp hl).1).2.symm

end

/-- **Lenstra–Shmoys–Tardos rounding theorem.** Let `p i j ∈ ℕ` be the processing time of job
`j` on machine `i`, and let `d i ∈ ℕ` (deadlines) and `t ∈ ℕ`. Suppose a fractional assignment
`x ≥ 0` uses only pairs with `p i j ≤ t`, assigns every job in total once
(`∑ᵢ x i j = 1`), and keeps every machine within its deadline (`∑ⱼ p i j x i j ≤ d i`). Then
there is an assignment `σ` of jobs to machines that uses only pairs with `p (σ j) j ≤ t` and
in which every machine `i` has load at most `d i + t`.

Source: J. K. Lenstra, D. B. Shmoys and É. Tardos, "Approximation algorithms for scheduling
unrelated parallel machines", Math. Programming 46 (1990), 259–271, Theorem 1 (rounding
theorem; there, any vertex of the LP can be so rounded, in polynomial time). -/
public theorem exists_assignment_load_le {M J : Type*} [Fintype M] [Fintype J] [DecidableEq M]
    (p : M → J → ℕ) (d : M → ℕ) (t : ℕ) (x : M → J → ℝ) (hx : ∀ i j, 0 ≤ x i j)
    (hsupp : ∀ i j, t < p i j → x i j = 0) (hjob : ∀ j, ∑ i, x i j = 1)
    (hload : ∀ i, ∑ j, (p i j : ℝ) * x i j ≤ d i) :
    ∃ σ : J → M, (∀ j, p (σ j) j ≤ t) ∧ ∀ i, ∑ j with σ j = i, p i j ≤ d i + t := by
  classical
  obtain ⟨f, hf, hslots⟩ := match_slots p x hx hjob
  have helig (j : J) : p (f j).1 j ≤ t := by
    by_contra! h
    exact ((mem_slots ..).1 (hslots j)).1.ne' (hsupp _ j h)
  refine ⟨fun j => (f j).1, helig, fun i => ?_⟩
  let s := univ.filter fun j => (f j).1 = i
  have hcap (j) (hj : j ∈ s) : p i j ≤ t := by
    simpa only [(mem_filter.mp hj).2] using helig j
  change ∑ j ∈ s, p i j ≤ d i + t
  suffices (∑ j ∈ s, (p i j : ℝ)) ≤ (d i : ℝ) + t by exact_mod_cast this
  calc
    ∑ j ∈ s, (p i j : ℝ) = ∑ k ∈ range t, ((s.filter fun j => k < p i j).card : ℝ) := by
      have h := sum_layers s (p i) (fun _ => 1) t
      simp only [sum_const, nsmul_eq_mul, mul_one] at h
      rw [h]
      exact sum_congr rfl fun j hj => congrArg Nat.cast (min_eq_right (hcap j hj)).symm
    _ ≤ ∑ k ∈ range t, (mass p x i (k + 1) + 1) := by
      refine sum_le_sum fun k _ => ?_
      have h : 0 ≤ mass p x i (k + 1) := sum_nonneg fun j _ => hx i j
      exact le_trans (by exact_mod_cast count_layer_le p x hx f hf hslots i k)
        (Nat.ceil_lt_add_one h).le
    _ = (∑ j, (min t (p i j) : ℕ) * x i j) + t := by
      rw [sum_add_distrib]
      simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
      exact congrArg (· + (t : ℝ)) (sum_layers univ (p i) (x i) t)
    _ ≤ (d i : ℝ) + t := by
      apply add_le_add_left
      refine le_trans (sum_le_sum fun j _ => ?_) (hload i)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_right t (p i j)) (hx i j)

end MathlibExt.ComputerScience.UnrelatedMachinesRoundingWanted
