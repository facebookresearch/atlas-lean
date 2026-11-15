/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Monotone.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Monotone.Monovary
import Mathlib.Order.OrderDual

/-!
# Discounted cumulative gain at a cutoff

For a finite candidate universe `Fin N`, real gains `g`, nonnegative
nonincreasing discounts `w`, and an injective ranked prefix `r`, discounted
cumulative gain is `∑ i, w i * g (r i)`. The ideal DCG uses the first `k`
entries of a full gain-sorted permutation. The main theorem
`dcgAt_le_idealDCGAt` bounds every injective prefix by that ideal prefix, and
`exists_sortedPerm` supplies the sorted permutation. Normalized DCG divides
actual DCG by ideal DCG, with value `0` when the ideal DCG is zero.

## Main declarations

* `dcgAt`: discounted cumulative gain of a ranked prefix.
* `idealDCGAt`: discounted cumulative gain of the first `k` entries of an ideal ranking.
* `dcgAt_le_idealDCGAt`: every injective prefix scores no more than the ideal ranking.
* `exists_sortedPerm`: every finite gain vector admits a gain-sorted permutation.
* `ndcgAt`: normalized discounted cumulative gain at a cutoff.
* `ndcgAt_mem_Icc`: normalized DCG lies in `[0, 1]` for nonnegative gains.
* `ndcgAt_sortedPrefix_eq_one_of_pos`: the sorted prefix has normalized DCG `1`
  when the ideal DCG is positive.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.InformationRetrieval

/-- Discounted cumulative gain of an injective ranked prefix.

The candidate universe is `Fin N`, gains are `g`, cutoff discounts are `w`,
and the ranked prefix is `r`. -/
noncomputable def dcgAt {N k : ℕ} (g : Fin N → ℝ) (w : Fin k → ℝ)
    (r : Fin k → Fin N) : ℝ :=
  ∑ i : Fin k, w i * g (r i)

/-- Discounted cumulative gain of the first `k` entries of an ideal ranking.

The discount vector is bundled with the validity conditions under which a
gain-sorted ranking is ideal: it is nonnegative and nonincreasing. The ranking
is bundled with sortedness: it is a permutation of the whole candidate
universe whose full gain sequence is nonincreasing. -/
noncomputable def idealDCGAt {N k : ℕ} (hk : k ≤ N) (g : Fin N → ℝ)
    (w : {w : Fin k → ℝ // (∀ i, 0 ≤ w i) ∧ Antitone w})
    (s : {s : Equiv.Perm (Fin N) // Antitone (g ∘ s)}) : ℝ :=
  ∑ i : Fin k, w.1 i * g (s.1 (Fin.castLE hk i))

private noncomputable def padW {N k : ℕ} (w : Fin k → ℝ) : Fin N → ℝ :=
  fun j => if h : (j : ℕ) < k then w ⟨j, h⟩ else 0

private theorem padW_castLE {N k : ℕ} (hk : k ≤ N) (w : Fin k → ℝ) (i : Fin k) :
    padW (N := N) w (Fin.castLE hk i) = w i := by
  simp [padW]

private theorem padW_eq_zero {N k : ℕ} (w : Fin k → ℝ) (j : Fin N) (hj : ¬ (j : ℕ) < k) :
    padW (N := N) w j = 0 := by
  simp [padW, hj]

private theorem padW_antitone {N k : ℕ} (w : Fin k → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw : Antitone w) : Antitone (padW (N := N) w) := by
  intro a b hab
  have hle : (a : ℕ) ≤ (b : ℕ) := Fin.le_iff_val_le_val.mp hab
  unfold padW
  by_cases ha : (a : ℕ) < k
  · by_cases hb : (b : ℕ) < k
    · simp only [ha, hb, dite_true]
      apply hw
      exact Fin.le_iff_val_le_val.mpr hle
    · simp only [ha, hb, dite_true, dite_false]
      exact hw0 _
  · by_cases hb : (b : ℕ) < k
    · exact absurd (lt_of_le_of_lt hle hb) ha
    · simp [ha, hb]

private theorem padW_sum {N k : ℕ} (hk : k ≤ N) (w : Fin k → ℝ) (H : Fin N → ℝ) :
    (∑ j : Fin N, padW (N := N) w j * H j)
      = ∑ i : Fin k, w i * H (Fin.castLE hk i) := by
  let e : Fin k ↪ Fin N := ⟨Fin.castLE hk, Fin.castLE_injective hk⟩
  have he : ∀ i : Fin k, e i = Fin.castLE hk i := fun i => rfl
  have hmem : ∀ j : Fin N, j ∈ Finset.univ.map e ↔ (j : ℕ) < k := by
    intro j
    constructor
    · intro hj
      rw [Finset.mem_map] at hj
      obtain ⟨i, _, rfl⟩ := hj
      rw [he, Fin.val_castLE]
      exact i.isLt
    · intro hj
      rw [Finset.mem_map]
      refine ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
      rw [he]
      apply Fin.ext
      simp
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      j ∉ Finset.univ.map e → padW (N := N) w j * H j = 0 := by
    intro j _ hjout
    have hnk : ¬ (j : ℕ) < k := by
      intro hlt
      exact hjout ((hmem j).mpr hlt)
    rw [padW_eq_zero w j hnk, zero_mul]
  have hsub : Finset.univ.map e ⊆ (Finset.univ : Finset (Fin N)) :=
    Finset.subset_univ _
  have hsum := Finset.sum_subset hsub hzero
  rw [Finset.sum_map] at hsum
  have hcongr : (∑ i : Fin k, padW (N := N) w (e i) * H (e i))
      = ∑ i : Fin k, w i * H (Fin.castLE hk i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [he, padW_castLE hk w i]
  rw [hcongr] at hsum
  exact hsum.symm

/-- Ideal top-`k` DCG bound.

For nonnegative nonincreasing discounts, an arbitrary injective ranked prefix
`r`, and a full gain-sorted bijection `s`, the DCG of `r` is at most the DCG of
the first `k` entries of `s`. -/
theorem dcgAt_le_idealDCGAt {N k : ℕ} (hk : k ≤ N)
    {g : Fin N → ℝ} {w : Fin k → ℝ} {r : Fin k → Fin N}
    {s : Equiv.Perm (Fin N)}
    (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w)
    (hr : Function.Injective r) (hs : Antitone (g ∘ s)) :
    dcgAt g w r ≤ idealDCGAt hk g ⟨w, ⟨hw0, hw⟩⟩ ⟨s, hs⟩ := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (Fin.castLE hk) r (Fin.castLE_injective hk) hr
  let τ : Equiv.Perm (Fin N) := σ.trans s.symm
  have hmono : Monovary (padW (N := N) w) (g ∘ s) :=
    Antitone.monovary (padW_antitone w hw0 hw) hs
  have hineq := Monovary.sum_mul_comp_perm_le_sum_mul (σ := τ) hmono
  have hLHS : (∑ j : Fin N, padW (N := N) w j * (g ∘ s) (τ j)) = dcgAt g w r := by
    have h1 : ∀ j : Fin N, (g ∘ s) (τ j) = g (σ j) := by
      intro j
      simp [τ]
    have h2 : (∑ j : Fin N, padW (N := N) w j * (g ∘ s) (τ j))
        = ∑ j : Fin N, padW (N := N) w j * g (σ j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [h1 j]
    rw [h2]
    rw [padW_sum hk w (fun j => g (σ j))]
    unfold dcgAt
    apply Finset.sum_congr rfl
    intro i _
    rw [hσ i]
  have hRHS : (∑ j : Fin N, padW (N := N) w j * (g ∘ s) j)
      = idealDCGAt hk g ⟨w, ⟨hw0, hw⟩⟩ ⟨s, hs⟩ := by
    rw [padW_sum hk w (g ∘ s)]
    unfold idealDCGAt
    rfl
  rw [hLHS, hRHS] at hineq
  exact hineq

/-- Every finite real gain vector has a full gain-sorted permutation. -/
theorem exists_sortedPerm {N : ℕ} (g : Fin N → ℝ) :
    ∃ s : Equiv.Perm (Fin N), Antitone (g ∘ s) := by
  refine ⟨Tuple.sort (OrderDual.toDual ∘ g), ?_⟩
  have h := Tuple.monotone_sort (OrderDual.toDual ∘ g)
  have h2 : Monotone (OrderDual.toDual ∘ (g ∘ Tuple.sort (OrderDual.toDual ∘ g))) := by
    simpa [Function.comp_assoc] using h
  exact (monotone_toDual_comp_iff).mp h2

/-- Normalized discounted cumulative gain at cutoff `k`.

This is `dcgAt` divided by `idealDCGAt` for the bundled valid discounts and
bundled sorted ranking. The selected convention when the ideal DCG is zero
is `0`. -/
noncomputable def ndcgAt {N k : ℕ} (hk : k ≤ N) (g : Fin N → ℝ)
    (w : {w : Fin k → ℝ // (∀ i, 0 ≤ w i) ∧ Antitone w})
    (r : Fin k → Fin N)
    (s : {s : Equiv.Perm (Fin N) // Antitone (g ∘ s)}) : ℝ :=
  if idealDCGAt hk g w s = 0 then 0
  else dcgAt g w.1 r / idealDCGAt hk g w s

/-- Normalized DCG is zero by convention when the ideal DCG is zero. -/
theorem ndcgAt_of_ideal_eq_zero {N k : ℕ} (hk : k ≤ N) (g : Fin N → ℝ)
    (w : {w : Fin k → ℝ // (∀ i, 0 ≤ w i) ∧ Antitone w})
    (r : Fin k → Fin N)
    (s : {s : Equiv.Perm (Fin N) // Antitone (g ∘ s)})
    (h : idealDCGAt hk g w s = 0) : ndcgAt hk g w r s = 0 := by
  unfold ndcgAt
  exact ite_eq_left h

/-- Normalized DCG lies in `[0, 1]` for nonnegative gains and an injective
ranked prefix. -/
theorem ndcgAt_mem_Icc {N k : ℕ} (hk : k ≤ N)
    {g : Fin N → ℝ}
    {w : {w : Fin k → ℝ // (∀ i, 0 ≤ w i) ∧ Antitone w}}
    {r : Fin k → Fin N}
    {s : {s : Equiv.Perm (Fin N) // Antitone (g ∘ s)}}
    (hg : ∀ i, 0 ≤ g i) (hr : Function.Injective r) :
    ndcgAt hk g w r s ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h0 : idealDCGAt hk g w s = 0
  · rw [ndcgAt_of_ideal_eq_zero hk g w r s h0, Set.mem_Icc]
    exact ⟨le_rfl, zero_le_one⟩
  · have hideal0 : 0 ≤ idealDCGAt hk g w s := by
      unfold idealDCGAt
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (w.2.1 i) (hg _)
    have hpos : 0 < idealDCGAt hk g w s := lt_of_le_of_ne hideal0 (Ne.symm h0)
    have hdcg0 : 0 ≤ dcgAt g w.1 r := by
      unfold dcgAt
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (w.2.1 i) (hg _)
    have hle : dcgAt g w.1 r ≤ idealDCGAt hk g w s :=
      dcgAt_le_idealDCGAt hk w.2.1 w.2.2 hr s.2
    unfold ndcgAt
    rw [ite_eq_right h0, Set.mem_Icc]
    exact ⟨div_nonneg hdcg0 (le_of_lt hpos), (div_le_one hpos).mpr hle⟩

/-- The sorted prefix has normalized DCG `1` when the ideal DCG is positive. -/
theorem ndcgAt_sortedPrefix_eq_one_of_pos {N k : ℕ} (hk : k ≤ N)
    (g : Fin N → ℝ)
    (w : {w : Fin k → ℝ // (∀ i, 0 ≤ w i) ∧ Antitone w})
    (s : {s : Equiv.Perm (Fin N) // Antitone (g ∘ s)})
    (hpos : 0 < idealDCGAt hk g w s) :
    ndcgAt hk g w (fun i => s.1 (Fin.castLE hk i)) s = 1 := by
  have hne : idealDCGAt hk g w s ≠ 0 := ne_of_gt hpos
  have hdcg : dcgAt g w.1 (fun i => s.1 (Fin.castLE hk i))
      = idealDCGAt hk g w s := rfl
  unfold ndcgAt
  rw [ite_eq_right hne, hdcg, div_self hne]

end Cslib.InformationRetrieval
