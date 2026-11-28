/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GlaisherOverpartitionDivisors

open MetaMathlibExt
open scoped ArithmeticFunction.sigma

local notation "dD" m:max => ∑ d ∈ Nat.divisors m with Odd (m / d), (d : ℤ)
local notation "σ₁" m:max => ((σ 1 m : ℕ) : ℤ)
local notation "σdiv" m:max => (if 2 ∣ m then ((σ 1 (m / 2) : ℕ) : ℤ) else 0)
local notation "pbar" m:max => ((Nat.card (Nat.Overpartition m) : ℕ) : ℤ)

private def squareIndices (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter (fun i ↦ i ^ 2 ≤ n)

-- Enumerate by removing one positive part, with a bound on the number of removals.
private def partMultisets : ℕ → ℕ → Finset (Multiset ℕ)
  | 0, n => if n = 0 then {0} else ∅
  | k + 1, n => if n = 0 then {0} else
      (Finset.Icc 1 n).biUnion fun a ↦ (partMultisets k (n - a)).image (Multiset.cons a)

private lemma mem_partMultisets {k n : ℕ} (hkn : n ≤ k) (s : Multiset ℕ) :
    s ∈ partMultisets k n ↔ (∀ a ∈ s, 0 < a) ∧ s.sum = n := by
  have hzero (s : Multiset ℕ) : s = 0 ↔ (∀ a ∈ s, 0 < a) ∧ s.sum = 0 := by
    refine ⟨fun h ↦ by simp [h], fun ⟨h, hs⟩ ↦ ?_⟩
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro a ha
    have := Multiset.le_sum_of_mem ha
    have := h a ha
    omega
  induction k generalizing n s with
  | zero =>
    have hn : n = 0 := by omega
    simpa [hn, partMultisets] using hzero s
  | succ k ih =>
    by_cases hn : n = 0
    · simpa [hn, partMultisets] using hzero s
    simp only [partMultisets, hn, ite_false, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨a, ⟨ha, han⟩, t, ht, rfl⟩
      obtain ⟨hpos, hsum⟩ := (ih (n := n - a) (by omega) t).mp ht
      simp only [Multiset.forall_mem_cons, Multiset.sum_cons]
      exact ⟨⟨ha, hpos⟩, by omega⟩
    · rintro ⟨hpos, hsum⟩
      have hs : s ≠ 0 := by rintro rfl; exact hn hsum.symm
      obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hs
      have hap := hpos a ha
      obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
      simp only [Multiset.forall_mem_cons, Multiset.sum_cons] at hpos hsum
      exact ⟨a, ⟨hap, by omega⟩, t, (ih (n := n - a) (by omega) t).mpr ⟨hpos.2, by omega⟩, rfl⟩

private lemma overpartitionCard_eq_enumeration (n : ℕ) :
    Nat.card (Nat.Overpartition n) = ∑ s ∈ partMultisets n n, 2 ^ s.toFinset.card := by
  let e : (Σ s : partMultisets n n, s.val.toFinset.powerset) ≃ Nat.Overpartition n :=
    { toFun := fun x ↦
        let h := (mem_partMultisets le_rfl x.1.val).mp x.1.property
        ⟨⟨x.1.val, fun ha ↦ h.1 _ ha, h.2⟩, x.2.val, Finset.mem_powerset.mp x.2.property⟩
      invFun := fun o ↦
        ⟨⟨o.toPartition.parts, (mem_partMultisets le_rfl _).mpr
          ⟨fun _ ha ↦ o.toPartition.parts_pos ha, o.toPartition.parts_sum⟩⟩,
          ⟨o.overlines, Finset.mem_powerset.mpr o.overlines_subset⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_coe, Finset.card_powerset]
  exact Finset.sum_coe_sort (partMultisets n n) (fun s : Multiset ℕ ↦ 2 ^ s.toFinset.card)

-- Evaluate all five expressions independently, using the finite overpartition enumeration.
private def formulasAt (n : ℕ) (first second : ℤ) : Prop :=
  2 * (dD n) = first ∧
  2 * ((σ₁ n) - σdiv n) = first ∧
  (n : ℤ) * pbar n + 2 * ∑ i ∈ squareIndices n,
    (-1) ^ i * ((n : ℤ) - (i : ℤ) ^ 2) * pbar (n - i ^ 2) = first ∧
  2 * ∑ i ∈ Finset.Icc 1 n, (dD (n - i)) * dD i = second ∧
  ∑ i ∈ squareIndices n,
    (-1) ^ (i + 1) * (i : ℤ) ^ 2 * ((n : ℤ) - (i : ℤ) ^ 2) * pbar (n - i ^ 2) = second

example : formulasAt 0 0 0 := by
  simp only [formulasAt, overpartitionCard_eq_enumeration]
  decide +kernel

example : formulasAt 2 4 2 := by
  simp only [formulasAt, overpartitionCard_eq_enumeration]
  decide +kernel

-- The second square occurs at the endpoint for `4`, and contributes nontrivially for `5`.
example : formulasAt 4 8 24 ∧ formulasAt 5 12 48 := by
  simp only [formulasAt, overpartitionCard_eq_enumeration]
  decide +kernel

-- Client of the moved theorem: exercise the public result with the original binders.
example : 2 * ∑ i ∈ Finset.Icc 1 5, (dD (5 - i)) * dD i =
    ∑ i ∈ squareIndices 5,
      (-1) ^ (i + 1) * (i : ℤ) ^ 2 * ((5 : ℤ) - (i : ℤ) ^ 2) * pbar (5 - i ^ 2) :=
  (overpartition_glaisher_dD_formulas (n := 5)).2
