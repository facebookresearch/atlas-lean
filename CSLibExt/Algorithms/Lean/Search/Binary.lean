/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Data.Array.Pairwise
public import Mathlib.Order.Defs.LinearOrder
import all Init.Data.Array.BinSearch

/-!
# Correctness of Lean array binary search

This file proves the public semantics of Lean 4.34.1's `Array.binSearch` and
`Array.binSearchContains` for a linear order. Search bounds are inclusive. An oversized upper
bound is clamped by the implementation to the final valid index.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

universe u

private abbrev orderedLt {α : Type u} [LinearOrder α] (a b : α) : Bool := decide (a < b)

private theorem pairwise_getElem_le {α : Type u} [LinearOrder α] {as : Array α}
    (hs : as.Pairwise (fun a b => a ≤ b)) {i j : Nat}
    (hi : i < as.size) (hj : j < as.size) (hij : i ≤ j) : as[i] ≤ as[j] := by
  obtain rfl | hij := Nat.eq_or_lt_of_le hij
  · exact le_rfl
  · exact Array.pairwise_iff_getElem.mp hs i j hi hj hij

private theorem binSearchAux_eq_if_mem {α : Type u} [LinearOrder α]
    (as : Array α) (hs : as.Pairwise (fun a b => a ≤ b)) (k : α)
    (lo : Fin (as.size + 1)) (hi : Fin as.size) (hlohi : lo.1 ≤ hi.1) :
    Array.binSearchAux orderedLt id as k lo hi hlohi =
      if ∃ i, ∃ h : i < as.size, lo.1 ≤ i ∧ i ≤ hi.1 ∧ as[i] = k then some k else none := by
  fun_induction Array.binSearchAux with
  | case1 lo hi _ m a halt hnext _ ih =>
      have halt' : a < k := by simpa [orderedLt] using halt
      have hm_size : m < as.size := by omega
      have hlo_m : lo.1 ≤ m := by omega
      have hiff :
          (∃ i, ∃ h : i < as.size, lo.1 ≤ i ∧ i ≤ hi.1 ∧ as[i] = k) ↔
            ∃ i, ∃ h : i < as.size, m + 1 ≤ i ∧ i ≤ hi.1 ∧ as[i] = k := by
        constructor
        · rintro ⟨i, hi_size, hlo_i, hi_i, hkey⟩
          have hm_i : m < i := by
            by_contra hnot
            have hi_m : i ≤ m := Nat.le_of_not_gt hnot
            have hle := pairwise_getElem_le hs hi_size hm_size hi_m
            have hka : k ≤ a := by simpa [a, hkey] using hle
            exact (not_le_of_gt halt') hka
          exact ⟨i, hi_size, by omega, hi_i, hkey⟩
        · rintro ⟨i, hi_size, hm_i, hi_i, hkey⟩
          exact ⟨i, hi_size, by omega, hi_i, hkey⟩
      rw [ih]
      split
      · rename_i hnew
        split
        · rfl
        · rename_i hold
          exact (hold (hiff.mpr hnew)).elim
      · rename_i hnew
        split
        · rename_i hold
          exact (hnew (hiff.mp hold)).elim
        · rfl
  | case2 lo hi _ m a halt hstop _ =>
      have halt' : a < k := by simpa [orderedLt] using halt
      have hm_size : m < as.size := by omega
      have hnone :
          ¬∃ i, ∃ h : i < as.size, lo.1 ≤ i ∧ i ≤ hi.1 ∧ as[i] = k := by
        rintro ⟨i, hi_size, _, hi_i, hkey⟩
        have hi_m : i ≤ m := by omega
        have hle := pairwise_getElem_le hs hi_size hm_size hi_m
        have hka : k ≤ a := by simpa [a, hkey] using hle
        exact (not_le_of_gt halt') hka
      simp only [id_eq]
      split
      · rename_i hmem
        exact (hnone hmem).elim
      · rfl
  | case3 lo hi _ m a _ hlt hstop _ =>
      have hlt' : k < a := by simpa [orderedLt] using hlt
      have hm_size : m < as.size := by omega
      have hnone :
          ¬∃ i, ∃ h : i < as.size, lo.1 ≤ i ∧ i ≤ hi.1 ∧ as[i] = k := by
        rintro ⟨i, hi_size, hlo_i, _, hkey⟩
        have hm_i : m ≤ i := by
          rcases hstop with hzero | hstop
          · omega
          · omega
        have hle := pairwise_getElem_le hs hm_size hi_size hm_i
        have hak : a ≤ k := by simpa [a, hkey] using hle
        exact (not_le_of_gt hlt') hak
      simp only [id_eq]
      split
      · rename_i hmem
        exact (hnone hmem).elim
      · rfl
  | case4 lo hi _ m a _ hlt hgo _ ih =>
      have hlt' : k < a := by simpa [orderedLt] using hlt
      have hm_size : m < as.size := by omega
      have hiff :
          (∃ i, ∃ h : i < as.size, lo.1 ≤ i ∧ i ≤ hi.1 ∧ as[i] = k) ↔
            ∃ i, ∃ h : i < as.size, lo.1 ≤ i ∧ i ≤ m - 1 ∧ as[i] = k := by
        constructor
        · rintro ⟨i, hi_size, hlo_i, hi_i, hkey⟩
          have hi_m : i < m := by
            by_contra hnot
            have hm_i : m ≤ i := Nat.le_of_not_gt hnot
            have hle := pairwise_getElem_le hs hm_size hi_size hm_i
            have hak : a ≤ k := by simpa [a, hkey] using hle
            exact (not_le_of_gt hlt') hak
          exact ⟨i, hi_size, hlo_i, by omega, hkey⟩
        · rintro ⟨i, hi_size, hlo_i, hi_m, hkey⟩
          exact ⟨i, hi_size, hlo_i, by omega, hkey⟩
      rw [ih]
      split
      · rename_i hnew
        split
        · rfl
        · rename_i hold
          exact (hold (hiff.mpr hnew)).elim
      · rename_i hnew
        split
        · rename_i hold
          exact (hnew (hiff.mp hold)).elim
        · rfl
  | case5 lo hi _ m a hnlt₁ hnlt₂ _ =>
      have hnlt₁' : ¬a < k := by simpa [orderedLt] using hnlt₁
      have hnlt₂' : ¬k < a := by simpa [orderedLt] using hnlt₂
      have ha : a = k := le_antisymm (le_of_not_gt hnlt₂') (le_of_not_gt hnlt₁')
      have hm_size : m < as.size := by omega
      have hex : ∃ i, ∃ h : i < as.size, lo.1 ≤ i ∧ i ≤ hi.1 ∧ as[i] = k :=
        ⟨m, hm_size, by omega, by omega, by simpa [a] using ha⟩
      simp only [id_eq]
      split
      · simp [ha]
      · rename_i hmem
        exact (hmem hex).elim

private theorem binSearch_eq_if_mem {α : Type} [LinearOrder α]
    (as : Array α) (hs : as.Pairwise (fun a b => a ≤ b)) (k : α)
    (lo hi : Nat) :
    as.binSearch k orderedLt lo hi =
      if ∃ i, ∃ h : i < as.size, lo ≤ i ∧ i ≤ hi ∧ as[i] = k then some k else none := by
  unfold Array.binSearch
  split
  · rename_i hlo
    dsimp
    split
    · rename_i hhi
      split
      · rw [binSearchAux_eq_if_mem as hs k]
      · rename_i hbad
        split
        · rename_i hmem
          obtain ⟨i, _, hlo_i, hi_i, _⟩ := hmem
          omega
        · rfl
    · rename_i hhi
      split
      · rw [binSearchAux_eq_if_mem as hs k]
        split
        · rename_i hclamp
          split
          · rfl
          · rename_i hraw
            obtain ⟨i, hi_size, hlo_i, _, hkey⟩ := hclamp
            exact (hraw ⟨i, hi_size, hlo_i, by omega, hkey⟩).elim
        · rename_i hclamp
          split
          · rename_i hraw
            obtain ⟨i, hi_size, hlo_i, _, hkey⟩ := hraw
            exact (hclamp ⟨i, hi_size, hlo_i, by change i ≤ as.size - 1; omega, hkey⟩).elim
          · rfl
      · omega
  · rename_i hlo
    split
    · rename_i hmem
      obtain ⟨i, hi_size, hlo_i, _, _⟩ := hmem
      omega
    · rfl

private theorem binSearchAux_map {α : Type u} {β : Type*}
    (lt : α → α → Bool) (found : Option α → β) (as : Array α) (k : α)
    (lo : Fin (as.size + 1)) (hi : Fin as.size) (hlohi : lo.1 ≤ hi.1) :
    Array.binSearchAux lt found as k lo hi hlohi =
      found (Array.binSearchAux lt id as k lo hi hlohi) := by
  fun_induction Array.binSearchAux lt found as k lo hi hlohi with
  | case1 lo hi hlohi m a hlt hnext _ ih =>
      rw [ih, Array.binSearchAux.eq_1 lt id as k lo hi hlohi]
      simp [m, a, hlt, hnext]
  | case2 lo hi hlohi m a hlt hstop _ =>
      rw [Array.binSearchAux.eq_1 lt id as k lo hi hlohi]
      simp [m, a, hlt, hstop]
  | case3 lo hi hlohi m a hnlt hlt hstop _ =>
      have hstop' : lo.1 + hi.1 < 2 ∨ (lo.1 + hi.1) / 2 - 1 < lo.1 := by
        rcases hstop with hzero | hsmall
        · left
          omega
        · right
          exact hsmall
      rw [Array.binSearchAux.eq_1 lt id as k lo hi hlohi]
      simp [m, a, hnlt, hlt, hstop']
  | case4 lo hi hlohi m a hnlt hlt hgo _ ih =>
      have hgo' : ¬(lo.1 + hi.1 < 2 ∨ (lo.1 + hi.1) / 2 - 1 < lo.1) := by
        rintro (hsmall | hsmall)
        · apply hgo
          left
          omega
        · exact hgo (Or.inr hsmall)
      rw [ih, Array.binSearchAux.eq_1 lt id as k lo hi hlohi]
      simp [m, a, hnlt, hlt, hgo']
  | case5 lo hi hlohi m a hnlt₁ hnlt₂ _ =>
      rw [Array.binSearchAux.eq_1 lt id as k lo hi hlohi]
      simp [m, a, hnlt₁, hnlt₂]

-- Note on universes: in Lean 4.34.1 core, `Array.binSearch` and
-- `Array.binSearchContains` both quantify `α : Type` (universe 0), verified by
-- `#check @Array.binSearch`. Only the auxiliary `Array.binSearchAux` is
-- universe-polymorphic, so the public theorems below necessarily match
-- core's universe-0 signatures.

/-- **Array binary search membership test agrees with binary search.** Let $A$ be an array with
entries in a type $\alpha$, let $k \in \alpha$, let $\mathrm{lt}$ be any Boolean-valued comparison
on $\alpha$, and let $\ell$ and $h$ be natural numbers. Lean core's Boolean binary search
membership test for $k$ in $A$, with comparison $\mathrm{lt}$ and bounds $\ell$ and $h$, returns
true exactly when Lean core's array binary search with the same arguments returns some element. -/
theorem binSearchContains_eq_isSome {α : Type} (as : Array α) (k : α)
    (lt : α → α → Bool) (lo hi : Nat) :
    as.binSearchContains k lt lo hi = (as.binSearch k lt lo hi).isSome := by
  unfold Array.binSearchContains Array.binSearch
  split
  · by_cases hhi : hi < as.size
    · by_cases hw : lo ≤ hi
      · simp [hhi, hw, binSearchAux_map (found := Option.isSome)]
      · simp [hhi, hw]
    · by_cases hw : lo ≤ as.size - 1
      · simp [hhi, hw, binSearchAux_map (found := Option.isSome)]
      · simp [hhi, hw]
  · rfl

/-- **Result of bounded binary search on a sorted array.** Let $A = (a_0, \dots, a_{n-1})$ be an
array of length $n$ with entries in a linearly ordered type, with $a_i \le a_j$ whenever $i < j$.
Let $k$ and $a$ be elements of that type and $\ell$, $h$ natural numbers. Lean core's array binary
search for $k$ in $A$, with the strict order $<$ as comparison and inclusive bounds $\ell$ and
$h$, returns $a$ if and only if $a = k$ and there is an index $i < n$ with $\ell \le i \le h$ and
$a_i = k$.

The requirement $i < n$ reflects the implementation's clamping of an upper bound $h \ge n$ to
$n - 1$. -/
theorem binSearch_eq_some_iff {α : Type} [LinearOrder α] {as : Array α}
    (hs : as.Pairwise (fun a b => a ≤ b)) {k a : α} {lo hi : Nat} :
    as.binSearch k (fun x y => decide (x < y)) lo hi = some a ↔
      a = k ∧ ∃ i, ∃ h : i < as.size, lo ≤ i ∧ i ≤ hi ∧ as[i] = k := by
  rw [binSearch_eq_if_mem as hs k lo hi]
  split
  · rename_i hmem
    constructor
    · intro heq
      exact ⟨(Option.some.inj heq).symm, hmem⟩
    · rintro ⟨ha, _⟩
      exact congrArg some ha.symm
  · rename_i hmem
    constructor
    · intro heq
      contradiction
    · rintro ⟨_, hmem'⟩
      exact (hmem hmem').elim

/-- **Bounded binary search on a sorted array fails exactly when the key is absent.** Let
$A = (a_0, \dots, a_{n-1})$ be an array of length $n$ with entries in a linearly ordered type,
with $a_i \le a_j$ whenever $i < j$. Let $k$ be an element of that type and $\ell$, $h$ natural
numbers. Lean core's array binary search for $k$ in $A$, with the strict order $<$ as comparison
and inclusive bounds $\ell$ and $h$, returns no element if and only if there is no index $i < n$
with $\ell \le i \le h$ and $a_i = k$. -/
theorem binSearch_eq_none_iff {α : Type} [LinearOrder α] {as : Array α}
    (hs : as.Pairwise (fun a b => a ≤ b)) {k : α} {lo hi : Nat} :
    as.binSearch k (fun x y => decide (x < y)) lo hi = none ↔
      ¬∃ i, ∃ h : i < as.size, lo ≤ i ∧ i ≤ hi ∧ as[i] = k := by
  rw [binSearch_eq_if_mem as hs k lo hi]
  simp

/-- **Bounded binary search membership test on a sorted array is correct.** Let
$A = (a_0, \dots, a_{n-1})$ be an array of length $n$ with entries in a linearly ordered type,
with $a_i \le a_j$ whenever $i < j$. Let $k$ be an element of that type and $\ell$, $h$ natural
numbers. Lean core's Boolean binary search membership test for $k$ in $A$, with the strict order
$<$ as comparison and inclusive bounds $\ell$ and $h$, returns true if and only if there is an
index $i < n$ with $\ell \le i \le h$ and $a_i = k$. -/
theorem binSearchContains_eq_true_iff {α : Type} [LinearOrder α] {as : Array α}
    (hs : as.Pairwise (fun a b => a ≤ b)) {k : α} {lo hi : Nat} :
    as.binSearchContains k (fun x y => decide (x < y)) lo hi = true ↔
      ∃ i, ∃ h : i < as.size, lo ≤ i ∧ i ≤ hi ∧ as[i] = k := by
  rw [binSearchContains_eq_isSome, binSearch_eq_if_mem as hs k lo hi]
  simp

private theorem fullRange_iff_mem {α : Type} [LinearOrder α] {as : Array α} {k : α} :
    (∃ i, ∃ h : i < as.size, 0 ≤ i ∧ i ≤ as.size - 1 ∧ as[i] = k) ↔ k ∈ as := by
  rw [Array.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, _, _, hkey⟩
    exact ⟨i, hi, hkey⟩
  · rintro ⟨i, hi, hkey⟩
    exact ⟨i, hi, Nat.zero_le i, by omega, hkey⟩

/-- **Binary search on a sorted array finds exactly its members.** Let $A$ be an array with entries
in a linearly ordered type, sorted so that an earlier entry is never greater than a later one, and
let $k$ and $a$ be elements of that type. Lean core's array binary search for $k$ over the whole of
$A$, with the strict order $<$ as comparison, returns $a$ if and only if $a = k$ and $k$ is an
entry of $A$. -/
theorem binSearch_eq_some_iff_mem {α : Type} [LinearOrder α] {as : Array α}
    (hs : as.Pairwise (fun a b => a ≤ b)) {k a : α} :
    as.binSearch k (fun x y => decide (x < y)) = some a ↔ a = k ∧ k ∈ as := by
  rw [binSearch_eq_some_iff hs, fullRange_iff_mem]

/-- **Binary search on a sorted array fails exactly on non-members.** Let $A$ be an array with
entries in a linearly ordered type, sorted so that an earlier entry is never greater than a later
one, and let $k$ be an element of that type. Lean core's array binary search for $k$ over the
whole of $A$, with the strict order $<$ as comparison, returns no element if and only if $k$ is
not an entry of $A$. -/
theorem binSearch_eq_none_iff_not_mem {α : Type} [LinearOrder α] {as : Array α}
    (hs : as.Pairwise (fun a b => a ≤ b)) {k : α} :
    as.binSearch k (fun x y => decide (x < y)) = none ↔ k ∉ as := by
  rw [binSearch_eq_none_iff hs, fullRange_iff_mem]

/-- **Binary search membership test on a sorted array is correct.** Let $A$ be an array with
entries in a linearly ordered type, sorted so that an earlier entry is never greater than a later
one, and let $k$ be an element of that type. Lean core's Boolean binary search membership test
for $k$ over the whole of $A$, with the strict order $<$ as comparison, returns true if and only
if $k$ is an entry of $A$. -/
theorem binSearchContains_eq_true_iff_mem {α : Type} [LinearOrder α] {as : Array α}
    (hs : as.Pairwise (fun a b => a ≤ b)) {k : α} :
    as.binSearchContains k (fun x y => decide (x < y)) = true ↔ k ∈ as := by
  rw [binSearchContains_eq_true_iff hs, fullRange_iff_mem]

end Cslib.Algorithms.Lean
