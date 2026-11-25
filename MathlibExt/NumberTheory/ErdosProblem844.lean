/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/844.lean` (Formal Conjectures), for the definitions and statement.
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Combinatorics.SetFamily.Intersecting
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Mathlib.NumberTheory.PrimeCounting

/-!
# Erdős Problem 844

`conjecture_holds` proves Erdős Problem 844: for every $N$, a largest set
$A \subseteq \{1, \dots, N\}$ such that $ab$ is not squarefree for all $a, b \in A$ consists of
the even numbers and the odd non-squarefree numbers in $\{1, \dots, N\}$. The proof follows
Weisenberg's argument, which deduces the bound from a theorem of Chvátal on intersecting
subfamilies of shifted down-sets; that theorem is `card_le_card_filter_zero_mem`, proved here by
compression and induction on the ground set.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem844Wanted

/-! Source record `FC-ErdosProblem844`, ported from FormalConjectures
`ErdosProblems/844.lean` and checked against erdosproblems.com/844.
The upstream `answer(True)` is dropped. Status: resolved true externally;
`conjecture_holds` below proves it, following Weisenberg's proof through Chvátal's theorem on
shifted down-sets. -/

/-- **Even or odd non-squarefree numbers up to a bound.** For a natural number $N$, the set of
integers $n$ with $1 \le n \le N$ that are even or not squarefree, that is, the even numbers in
$\{1, \dots, N\}$ together with the odd non-squarefree numbers in $\{1, \dots, N\}$. -/
def evenOrOddNonSquarefree (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => 2 ∣ n ∨ ¬ Squarefree n)

/-- **Erdős Problem 844.** For a natural number $N$, let $E_N$ be the set of integers $n$ with
$1 \le n \le N$ that are even or not squarefree. The statement that for every natural number $N$,
the largest size of a set $A \subseteq \{1, \dots, N\}$ such that $ab$ is not squarefree for all
$a, b \in A$ (including $a = b$) is the size of $E_N$. -/
def conjecture : Prop :=
  ∀ N : ℕ,
    IsGreatest {k : ℕ | ∃ A ⊆ Finset.Icc 1 N,
      (∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b)) ∧ A.card = k}
      (evenOrOddNonSquarefree N).card

open Finset

/-! ### Chvátal's theorem for shifted down-sets -/

section Chvatal

/-- A family is shifted at `m` when replacing `m` in a member by a smaller absent element gives
another member. -/
private def ShiftedAt (m : ℕ) (𝓐 : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ 𝓐, m ∈ A → ∀ i < m, i ∉ A → insert i (A.erase m) ∈ 𝓐

private lemma compress_singleton_eq {i m : ℕ} (him : i ≠ m) (A : Finset ℕ) :
    UV.compress ({i} : Finset ℕ) {m} A = if i ∉ A ∧ m ∈ A then insert i (A.erase m) else A := by
  unfold UV.compress
  simp only [disjoint_singleton_left, singleton_subset_iff]
  split_ifs with h
  · ext x
    simp only [mem_sdiff, mem_union, mem_singleton, mem_insert, mem_erase]
    constructor
    · rintro ⟨hx | rfl, hxm⟩
      · exact Or.inr ⟨hxm, hx⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨hxm, hx⟩)
      · exact ⟨Or.inr rfl, him⟩
      · exact ⟨Or.inl hx, hxm⟩
  · rfl

/-- The members of the compression of `𝓐` moving `m` to `i`: unmoved members of `𝓐`, whose
compression is already in `𝓐` when it applies, and moved images not in `𝓐`. -/
private lemma mem_compression_singleton {i m : ℕ} (him : i ≠ m) {𝓐 : Finset (Finset ℕ)}
    {B : Finset ℕ} (hB : B ∈ UV.compression {i} {m} 𝓐) :
    B ∈ 𝓐 ∧ (m ∈ B → i ∉ B → insert i (B.erase m) ∈ 𝓐) ∨
      B ∉ 𝓐 ∧ ∃ A ∈ 𝓐, m ∈ A ∧ i ∉ A ∧ B = insert i (A.erase m) := by
  rw [UV.mem_compression] at hB
  rcases hB with ⟨hB, hc⟩ | ⟨hB, A, hA, hc⟩
  · refine Or.inl ⟨hB, fun hm hi => ?_⟩
    rwa [compress_singleton_eq him, ite_eq_left ⟨hi, hm⟩] at hc
  · refine Or.inr ⟨hB, A, hA, ?_⟩
    rw [compress_singleton_eq him] at hc
    split_ifs at hc with h
    · exact ⟨h.2, h.1, hc.symm⟩
    · exact absurd (hc ▸ hA) hB

/-- An unmoved member meets every moved member. -/
private lemma not_disjoint_insert_erase {i m : ℕ} {𝓐 : Finset (Finset ℕ)}
    (hint : (𝓐 : Set (Finset ℕ)).Intersecting) {B A : Finset ℕ} (hB : B ∈ 𝓐)
    (hB' : m ∈ B → i ∉ B → insert i (B.erase m) ∈ 𝓐) (hA : A ∈ 𝓐) (hiA : i ∉ A) :
    ¬ Disjoint B (insert i (A.erase m)) := by
  intro hdis
  have hiB : i ∉ B := fun h => disjoint_left.1 hdis h (mem_insert_self _ _)
  have hmB : m ∈ B := by
    by_contra hmB
    refine hint hB hA (disjoint_left.2 fun x hxB hxA => ?_)
    have hxm : x ≠ m := fun h => hmB (h ▸ hxB)
    exact disjoint_left.1 hdis hxB (mem_insert_of_mem (mem_erase.2 ⟨hxm, hxA⟩))
  refine hint (hB' hmB hiB) hA (disjoint_left.2 fun x hx hxA => ?_)
  rcases mem_insert.1 hx with rfl | hx
  · exact hiA hxA
  · obtain ⟨hxm, hxB⟩ := mem_erase.1 hx
    exact disjoint_left.1 hdis hxB (mem_insert_of_mem (mem_erase.2 ⟨hxm, hxA⟩))

/-- Compression preserves the intersecting property. -/
private lemma intersecting_compression {i m : ℕ} (him : i ≠ m) {𝓐 : Finset (Finset ℕ)}
    (hint : (𝓐 : Set (Finset ℕ)).Intersecting) :
    ((UV.compression {i} {m} 𝓐 : Finset (Finset ℕ)) : Set (Finset ℕ)).Intersecting := by
  intro B hB C hC hBC
  rcases mem_compression_singleton him hB with ⟨hB, hB'⟩ | ⟨-, A, hA, -, hiA, rfl⟩ <;>
    rcases mem_compression_singleton him hC with ⟨hC, hC'⟩ | ⟨-, A', hA', -, hiA', rfl⟩
  · exact hint hB hC hBC
  · exact not_disjoint_insert_erase hint hB hB' hA' hiA' hBC
  · exact not_disjoint_insert_erase hint hC hC' hA hiA hBC.symm
  · exact disjoint_left.1 hBC (mem_insert_self i _) (mem_insert_self i _)

/-- Compression keeps a subfamily of a shifted family inside it. -/
private lemma compression_subset {i m : ℕ} (him : i < m) {𝓕 𝓐 : Finset (Finset ℕ)}
    (hshift : ∀ A ∈ 𝓕, ∀ j ∈ A, ∀ i < j, i ∉ A → insert i (A.erase j) ∈ 𝓕)
    (h𝓐 : 𝓐 ⊆ 𝓕) : UV.compression {i} {m} 𝓐 ⊆ 𝓕 := by
  intro B hB
  rcases mem_compression_singleton him.ne hB with ⟨hB, -⟩ | ⟨-, A, hA, hmA, hiA, rfl⟩
  · exact h𝓐 hB
  · exact hshift A (h𝓐 hA) m hmA i him hiA

/-- A compression that moves some member decreases the number of members containing `m`. -/
private lemma card_filter_mem_compression_lt {i m : ℕ} (him : i ≠ m) {𝓐 : Finset (Finset ℕ)}
    {A : Finset ℕ} (hA : A ∈ 𝓐) (hmA : m ∈ A) (hiA : i ∉ A)
    (hnot : insert i (A.erase m) ∉ 𝓐) :
    #{B ∈ UV.compression {i} {m} 𝓐 | m ∈ B} < #{B ∈ 𝓐 | m ∈ B} := by
  apply card_lt_card
  rw [ssubset_iff_of_subset]
  · refine ⟨A, mem_filter.2 ⟨hA, hmA⟩, fun h => ?_⟩
    rcases mem_compression_singleton him (mem_filter.1 h).1 with ⟨-, hA'⟩ | ⟨hA', -⟩
    · exact hnot (hA' hmA hiA)
    · exact hA' hA
  · intro B hB
    obtain ⟨hB, hmB⟩ := mem_filter.1 hB
    rcases mem_compression_singleton him hB with ⟨hB, -⟩ | ⟨-, A', -, -, -, rfl⟩
    · exact mem_filter.2 ⟨hB, hmB⟩
    · exfalso
      rcases mem_insert.1 hmB with h | h
      · exact him h.symm
      · exact notMem_erase m A' h

/-- Every intersecting subfamily of a shifted family can be replaced by one of the same size that
is shifted at `m`. -/
private lemma exists_shiftedAt {𝓕 : Finset (Finset ℕ)}
    (hshift : ∀ A ∈ 𝓕, ∀ j ∈ A, ∀ i < j, i ∉ A → insert i (A.erase j) ∈ 𝓕) (m : ℕ)
    (𝓐 : Finset (Finset ℕ)) (h𝓐 : 𝓐 ⊆ 𝓕) (hint : (𝓐 : Set (Finset ℕ)).Intersecting) :
    ∃ 𝓑 : Finset (Finset ℕ), 𝓑 ⊆ 𝓕 ∧ (𝓑 : Set (Finset ℕ)).Intersecting ∧ #𝓑 = #𝓐 ∧
      ShiftedAt m 𝓑 := by
  suffices H : ∀ k, ∀ 𝓐 : Finset (Finset ℕ), #{B ∈ 𝓐 | m ∈ B} = k → 𝓐 ⊆ 𝓕 →
      (𝓐 : Set (Finset ℕ)).Intersecting →
      ∃ 𝓑 : Finset (Finset ℕ), 𝓑 ⊆ 𝓕 ∧ (𝓑 : Set (Finset ℕ)).Intersecting ∧ #𝓑 = #𝓐 ∧
        ShiftedAt m 𝓑 from H _ 𝓐 rfl h𝓐 hint
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro 𝓐 hk h𝓐 hint
    by_cases hs : ShiftedAt m 𝓐
    · exact ⟨𝓐, h𝓐, hint, rfl, hs⟩
    · simp only [ShiftedAt, not_forall] at hs
      obtain ⟨A, hA, hmA, i, him, hiA, hnot⟩ := hs
      obtain ⟨𝓑, h𝓑, hint𝓑, hcard, hsh⟩ :=
        ih _ (hk ▸ card_filter_mem_compression_lt him.ne hA hmA hiA hnot)
          (UV.compression {i} {m} 𝓐) rfl (compression_subset him hshift h𝓐)
          (intersecting_compression him.ne hint)
      exact ⟨𝓑, h𝓑, hint𝓑, hcard.trans (UV.card_compression _ _ _), hsh⟩

/-- In a family shifted at `m` whose members lie in `{0, ..., m}`, two members containing `m`
that meet only in `m` together cover `{0, ..., m}`. -/
private lemma union_eq_range_of_disjoint {m : ℕ} {𝓑 : Finset (Finset ℕ)}
    (hint : (𝓑 : Set (Finset ℕ)).Intersecting) (hsh : ShiftedAt m 𝓑)
    (hbd : ∀ A ∈ 𝓑, A ⊆ range (m + 1)) {X Y : Finset ℕ}
    (hX : X ∈ 𝓑.memberSubfamily m) (hY : Y ∈ 𝓑.memberSubfamily m) (hXY : Disjoint X Y) :
    X ∪ Y = range m := by
  rw [mem_memberSubfamily] at hX hY
  have hsub : ∀ Z, insert m Z ∈ 𝓑 → m ∉ Z → Z ⊆ range m := fun Z hZ hmZ x hx => by
    have hx' := mem_range.1 (hbd _ hZ (mem_insert_of_mem hx))
    exact mem_range.2 (lt_of_le_of_ne (Nat.lt_succ_iff.1 hx') fun h => hmZ (h ▸ hx))
  refine Subset.antisymm (union_subset (hsub X hX.1 hX.2) (hsub Y hY.1 hY.2)) fun i hi => ?_
  by_contra hiXY
  rw [mem_union, not_or] at hiXY
  have hi' : i < m := mem_range.1 hi
  have hmem : insert i ((insert m Y).erase m) ∈ 𝓑 :=
    hsh _ hY.1 (mem_insert_self m Y) i hi' (by simp [hiXY.2, hi'.ne])
  rw [erase_insert hY.2] at hmem
  refine hint hX.1 hmem (disjoint_left.2 fun x hx hx' => ?_)
  rcases mem_insert.1 hx with rfl | hx
  · rcases mem_insert.1 hx' with h | h
    · exact hi'.ne h.symm
    · exact hY.2 h
  · rcases mem_insert.1 hx' with rfl | h
    · exact hiXY.1 hx
    · exact disjoint_left.1 hXY hx h

private lemma isLowerSet_memberSubfamily {m : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hlow : IsLowerSet (𝓕 : Set (Finset ℕ))) :
    IsLowerSet ((𝓕.memberSubfamily m : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
  intro X Y hYX hX
  rw [mem_coe, mem_memberSubfamily] at hX ⊢
  exact ⟨hlow (insert_subset_insert m hYX) hX.1, fun h => hX.2 (hYX h)⟩

private lemma isLowerSet_nonMemberSubfamily {m : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hlow : IsLowerSet (𝓕 : Set (Finset ℕ))) :
    IsLowerSet ((𝓕.nonMemberSubfamily m : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
  intro X Y hYX hX
  rw [mem_coe, mem_nonMemberSubfamily] at hX ⊢
  exact ⟨hlow hYX hX.1, fun h => hX.2 (hYX h)⟩

private lemma shift_memberSubfamily {m : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hshift : ∀ A ∈ 𝓕, ∀ j ∈ A, ∀ i < j, i ∉ A → insert i (A.erase j) ∈ 𝓕)
    (hbd : ∀ A ∈ 𝓕, A ⊆ range (m + 1)) :
    ∀ A ∈ 𝓕.memberSubfamily m, ∀ j ∈ A, ∀ i < j, i ∉ A →
      insert i (A.erase j) ∈ 𝓕.memberSubfamily m := by
  intro A hA j hj i hij hiA
  rw [mem_memberSubfamily] at hA ⊢
  have hjm : j ≠ m := fun h => hA.2 (h ▸ hj)
  have hjm' : j < m :=
    lt_of_le_of_ne (Nat.lt_succ_iff.1 (mem_range.1 (hbd _ hA.1 (mem_insert_of_mem hj)))) hjm
  have him : i ≠ m := (hij.trans hjm').ne
  have h := hshift _ hA.1 j (mem_insert_of_mem hj) i hij (by simp [him, hiA])
  rw [erase_insert_of_ne (Ne.symm hjm), insert_comm] at h
  refine ⟨h, ?_⟩
  simp [him.symm, hA.2]

private lemma shift_nonMemberSubfamily {m : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hshift : ∀ A ∈ 𝓕, ∀ j ∈ A, ∀ i < j, i ∉ A → insert i (A.erase j) ∈ 𝓕)
    (hbd : ∀ A ∈ 𝓕, A ⊆ range (m + 1)) :
    ∀ A ∈ 𝓕.nonMemberSubfamily m, ∀ j ∈ A, ∀ i < j, i ∉ A →
      insert i (A.erase j) ∈ 𝓕.nonMemberSubfamily m := by
  intro A hA j hj i hij hiA
  rw [mem_nonMemberSubfamily] at hA ⊢
  have hjm : j ≠ m := fun h => hA.2 (h ▸ hj)
  have hjm' : j < m := lt_of_le_of_ne (Nat.lt_succ_iff.1 (mem_range.1 (hbd _ hA.1 hj))) hjm
  have him : i ≠ m := (hij.trans hjm').ne
  refine ⟨hshift _ hA.1 j hj i hij hiA, ?_⟩
  simp [him.symm, hA.2]

private lemma subset_range_memberSubfamily {m : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hbd : ∀ A ∈ 𝓕, A ⊆ range (m + 1)) : ∀ A ∈ 𝓕.memberSubfamily m, A ⊆ range m := by
  intro A hA x hx
  rw [mem_memberSubfamily] at hA
  have hx' := mem_range.1 (hbd _ hA.1 (mem_insert_of_mem hx))
  exact mem_range.2 (lt_of_le_of_ne (Nat.lt_succ_iff.1 hx') fun h => hA.2 (h ▸ hx))

private lemma subset_range_nonMemberSubfamily {m : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hbd : ∀ A ∈ 𝓕, A ⊆ range (m + 1)) : ∀ A ∈ 𝓕.nonMemberSubfamily m, A ⊆ range m := by
  intro A hA x hx
  rw [mem_nonMemberSubfamily] at hA
  have hx' := mem_range.1 (hbd _ hA.1 hx)
  exact mem_range.2 (lt_of_le_of_ne (Nat.lt_succ_iff.1 hx') fun h => hA.2 (h ▸ hx))

/-- Chvátal's bound for families whose members lie in `{0, ..., n - 1}`, by induction on `n`. -/
private lemma card_le_aux (n : ℕ) :
    ∀ 𝓕 𝓐 : Finset (Finset ℕ), IsLowerSet (𝓕 : Set (Finset ℕ)) →
      (∀ A ∈ 𝓕, ∀ j ∈ A, ∀ i < j, i ∉ A → insert i (A.erase j) ∈ 𝓕) →
      (∀ A ∈ 𝓕, A ⊆ range n) → 𝓐 ⊆ 𝓕 → (𝓐 : Set (Finset ℕ)).Intersecting →
      #𝓐 ≤ #{A ∈ 𝓕 | 0 ∈ A} := by
  induction n with
  | zero =>
    intro 𝓕 𝓐 _ _ hbd h𝓐 hint
    refine card_le_card fun A hA => ?_
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 (hint.ne_bot hA)
    simpa using hbd A (h𝓐 hA) hx
  | succ m ih =>
    intro 𝓕 𝓐 hlow hshift hbd h𝓐 hint
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine card_le_card fun A hA => mem_filter.2 ⟨h𝓐 hA, ?_⟩
      obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 (hint.ne_bot hA)
      have hx0 : x = 0 := by simpa using hbd A (h𝓐 hA) hx
      exact hx0 ▸ hx
    obtain ⟨𝓑, h𝓑, hint𝓑, hcard, hsh⟩ := exists_shiftedAt hshift m 𝓐 h𝓐 hint
    have hbd𝓑 : ∀ A ∈ 𝓑, A ⊆ range (m + 1) := fun A hA => hbd A (h𝓑 hA)
    rw [← hcard]
    -- Split `𝓑` according to whether its members contain `m`.
    set 𝓒 := (𝓑.memberSubfamily m).filter
      (fun X => 0 ∉ X ∧ range m \ X ∈ 𝓑.memberSubfamily m)
    set 𝓓 := (𝓑.memberSubfamily m).filter
      (fun X => ¬ (0 ∉ X ∧ range m \ X ∈ 𝓑.memberSubfamily m))
    have h0m : 0 ∈ range m := mem_range.2 hm
    -- Members of `𝓓` pairwise intersect.
    have hint𝓓 : (𝓓 : Set (Finset ℕ)).Intersecting := by
      intro X hX Y hY hXY
      obtain ⟨hX, hpX⟩ := mem_filter.1 hX
      obtain ⟨hY, hpY⟩ := mem_filter.1 hY
      have hU := union_eq_range_of_disjoint hint𝓑 hsh hbd𝓑 hX hY hXY
      rcases mem_union.1 (hU ▸ h0m) with h0X | h0Y
      · refine hpY ⟨fun h0Y => disjoint_left.1 hXY h0X h0Y, ?_⟩
        rwa [← hU, union_sdiff_right, hXY.sdiff_eq_left]
      · refine hpX ⟨fun h0X => disjoint_left.1 hXY h0X h0Y, ?_⟩
        rwa [← hU, union_sdiff_left, hXY.symm.sdiff_eq_left]
    -- Members of `𝓑` without `m`, together with `𝓒`, pairwise intersect.
    have hint𝓒 : ((𝓑.nonMemberSubfamily m ∪ 𝓒 : Finset (Finset ℕ)) :
        Set (Finset ℕ)).Intersecting := by
      intro A hA B hB hAB
      rw [mem_coe, mem_union] at hA hB
      rcases hA with hA | hA <;> rcases hB with hB | hB
      · exact hint𝓑 (mem_nonMemberSubfamily.1 hA).1 (mem_nonMemberSubfamily.1 hB).1 hAB
      · obtain ⟨hA, hmA⟩ := mem_nonMemberSubfamily.1 hA
        exact hint𝓑 hA (mem_memberSubfamily.1 (mem_filter.1 hB).1).1
          (disjoint_insert_right.2 ⟨hmA, hAB⟩)
      · obtain ⟨hB, hmB⟩ := mem_nonMemberSubfamily.1 hB
        exact hint𝓑 (mem_memberSubfamily.1 (mem_filter.1 hA).1).1 hB
          (disjoint_insert_left.2 ⟨hmB, hAB⟩)
      · obtain ⟨hA, h0A, -⟩ := mem_filter.1 hA
        obtain ⟨hB, h0B, -⟩ := mem_filter.1 hB
        have hU := union_eq_range_of_disjoint hint𝓑 hsh hbd𝓑 hA hB hAB
        rcases mem_union.1 (hU ▸ h0m) with h | h
        · exact h0A h
        · exact h0B h
    have hdisj : Disjoint (𝓑.nonMemberSubfamily m) 𝓒 := by
      refine disjoint_left.2 fun X hX hXC => ?_
      obtain ⟨hX, hmX⟩ := mem_nonMemberSubfamily.1 hX
      obtain ⟨-, -, hcomp⟩ := mem_filter.1 hXC
      exact hint𝓑 hX (mem_memberSubfamily.1 hcomp).1
        (disjoint_insert_right.2 ⟨hmX, disjoint_sdiff⟩)
    -- Apply the induction hypothesis to both parts.
    have hD : #𝓓 ≤ #{A ∈ 𝓕.memberSubfamily m | 0 ∈ A} := by
      refine ih _ _ (isLowerSet_memberSubfamily hlow) (shift_memberSubfamily hshift hbd)
        (subset_range_memberSubfamily hbd) (fun X hX => ?_) hint𝓓
      rw [mem_memberSubfamily]
      obtain ⟨hX, -⟩ := mem_filter.1 hX
      rw [mem_memberSubfamily] at hX
      exact ⟨h𝓑 hX.1, hX.2⟩
    have hC : #(𝓑.nonMemberSubfamily m ∪ 𝓒) ≤ #{A ∈ 𝓕.nonMemberSubfamily m | 0 ∈ A} := by
      refine ih _ _ (isLowerSet_nonMemberSubfamily hlow) (shift_nonMemberSubfamily hshift hbd)
        (subset_range_nonMemberSubfamily hbd) (fun X hX => ?_) hint𝓒
      rw [mem_nonMemberSubfamily]
      rcases mem_union.1 hX with hX | hX
      · obtain ⟨hX, hmX⟩ := mem_nonMemberSubfamily.1 hX
        exact ⟨h𝓑 hX, hmX⟩
      · obtain ⟨hX, -⟩ := mem_filter.1 hX
        rw [mem_memberSubfamily] at hX
        exact ⟨hlow (subset_insert m X) (h𝓑 hX.1), hX.2⟩
    rw [card_union_of_disjoint hdisj] at hC
    -- Count the star of `0` in `𝓕` by the same split.
    have hstar : #{A ∈ 𝓕 | 0 ∈ A} =
        #{A ∈ 𝓕.memberSubfamily m | 0 ∈ A} + #{A ∈ 𝓕.nonMemberSubfamily m | 0 ∈ A} := by
      rw [← card_memberSubfamily_add_card_nonMemberSubfamily m {A ∈ 𝓕 | 0 ∈ A}]
      congr 2
      · ext X
        simp only [mem_memberSubfamily, mem_filter, mem_insert]
        constructor
        · rintro ⟨⟨hX, h0 | h0⟩, hmX⟩
          · exact absurd h0 hm.ne
          · exact ⟨⟨hX, hmX⟩, h0⟩
        · rintro ⟨⟨hX, hmX⟩, h0⟩
          exact ⟨⟨hX, Or.inr h0⟩, hmX⟩
      · ext X
        simp only [mem_nonMemberSubfamily, mem_filter]
        tauto
    have hsplit : #(𝓑.memberSubfamily m) = #𝓒 + #𝓓 :=
      (card_filter_add_card_filter_not _).symm
    rw [hstar, ← card_memberSubfamily_add_card_nonMemberSubfamily m 𝓑, hsplit]
    omega

/-- **Chvátal's theorem for shifted down-sets.** Let $\mathcal F$ be a finite family of finite
sets of natural numbers that is closed under taking subsets and under shifting, that is,
replacing an element $j$ of a member by a smaller natural number $i$ not in that member gives
another member. Then every intersecting subfamily of $\mathcal F$ (any two members, equal or not,
meet) has at most as many members as the star $\{A \in \mathcal F : 0 \in A\}$.

The proof compresses the intersecting family at the largest element $m$ of the ground set and
splits it by whether its members contain $m$; induction on the ground set applies to both parts.

Source: B. Alexeev, D. Mixon, and W. Sawin, The independence and clique cover numbers of the
squarefree graph, arXiv:2507.01928 (2025), https://arxiv.org/abs/2507.01928, Section 1.1,
Proposition 3, where the result is attributed to V. Chvátal, Intersecting families of edges in
hypergraphs having the hereditary property, Hypergraph Seminar, Springer (1974), 61-66. There
the ground set is $\{1, \dots, k\}$, the star is that of $1$, and the family is closed under
passing to any set that injects into a member by a map $f$ with $x \le f(x)$, which is
equivalent to closure under subsets and shifts. -/
theorem card_le_card_filter_zero_mem {𝓕 𝓐 : Finset (Finset ℕ)}
    (hlow : IsLowerSet (𝓕 : Set (Finset ℕ)))
    (hshift : ∀ A ∈ 𝓕, ∀ j ∈ A, ∀ i < j, i ∉ A → insert i (A.erase j) ∈ 𝓕)
    (h𝓐 : 𝓐 ⊆ 𝓕) (hint : (𝓐 : Set (Finset ℕ)).Intersecting) :
    #𝓐 ≤ #{A ∈ 𝓕 | 0 ∈ A} := by
  refine card_le_aux (𝓕.sup fun A => A.sup (· + 1)) 𝓕 𝓐 hlow hshift (fun A hA x hx => ?_) h𝓐
    hint
  have h₁ : x + 1 ≤ A.sup (· + 1) := le_sup (f := (· + 1)) hx
  have h₂ : A.sup (· + 1) ≤ 𝓕.sup fun A => A.sup (· + 1) :=
    le_sup (f := fun A : Finset ℕ => A.sup (· + 1)) hA
  exact mem_range.2 (by omega)

end Chvatal

/-! ### Squarefree numbers as sets of prime indices -/

section PrimeIndices

/-- The product of the primes $p_i$ over the indices $i \in A$, where $p_0 = 2$. -/
private noncomputable def primeProd (A : Finset ℕ) : ℕ := ∏ i ∈ A, Nat.nth Nat.Prime i

/-- The indices of the prime factors of $n$. -/
private def primeIdx (n : ℕ) : Finset ℕ := n.primeFactors.image (Nat.count Nat.Prime)

private lemma nth_prime_injective : Function.Injective (Nat.nth Nat.Prime) :=
  Nat.nth_injective (p := Nat.Prime) Nat.infinite_setOfPred_prime

private lemma nth_prime_strictMono : StrictMono (Nat.nth Nat.Prime) :=
  Nat.nth_strictMono (p := Nat.Prime) Nat.infinite_setOfPred_prime

private lemma primeProd_eq_prod_image (A : Finset ℕ) :
    primeProd A = ∏ p ∈ A.image (Nat.nth Nat.Prime), p := by
  rw [primeProd, prod_image fun i _ j _ h => nth_prime_injective h]

private lemma primeFactors_primeProd (A : Finset ℕ) :
    (primeProd A).primeFactors = A.image (Nat.nth Nat.Prime) := by
  rw [primeProd_eq_prod_image]
  refine Nat.primeFactors_prod fun p hp => ?_
  obtain ⟨i, -, rfl⟩ := mem_image.1 hp
  exact Nat.prime_nth_prime i

private lemma squarefree_primeProd (A : Finset ℕ) : Squarefree (primeProd A) := by
  have h := Nat.squarefree_prod_primeFactors (primeProd A)
  rwa [primeFactors_primeProd, ← primeProd_eq_prod_image] at h

private lemma primeProd_pos (A : Finset ℕ) : 0 < primeProd A :=
  prod_pos fun i _ => (Nat.prime_nth_prime i).pos

private lemma primeIdx_primeProd (A : Finset ℕ) : primeIdx (primeProd A) = A := by
  rw [primeIdx, primeFactors_primeProd, image_image]
  conv_rhs => rw [← image_id (s := A)]
  exact image_congr fun i _ =>
    Nat.count_nth_of_infinite (p := Nat.Prime) Nat.infinite_setOfPred_prime i

private lemma primeProd_primeIdx {n : ℕ} (hn : Squarefree n) : primeProd (primeIdx n) = n := by
  have hinj : Set.InjOn (Nat.count Nat.Prime) n.primeFactors := fun p hp q hq h =>
    Nat.count_injective (p := Nat.Prime) (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq) h
  rw [primeProd, primeIdx, prod_image hinj]
  conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hn]
  exact prod_congr rfl fun p hp => Nat.nth_count (Nat.prime_of_mem_primeFactors hp)

private lemma primeProd_le_of_subset {A B : Finset ℕ} (h : B ⊆ A) : primeProd B ≤ primeProd A :=
  prod_le_prod_of_subset_of_one_le h fun i _ _ => (Nat.prime_nth_prime i).one_lt.le

private lemma primeProd_shift_le {A : Finset ℕ} {i j : ℕ} (hj : j ∈ A) (hij : i < j)
    (hiA : i ∉ A) : primeProd (insert i (A.erase j)) ≤ primeProd A := by
  have hi : i ∉ A.erase j := fun h => hiA (mem_of_mem_erase h)
  unfold primeProd
  rw [prod_insert hi, ← mul_prod_erase A _ hj]
  exact Nat.mul_le_mul_right _ (nth_prime_strictMono hij).le

private lemma add_two_le_primeProd {A : Finset ℕ} {i : ℕ} (hi : i ∈ A) : i + 2 ≤ primeProd A :=
  (Nat.add_two_le_nth_prime i).trans
    (Nat.le_of_dvd (primeProd_pos A) (dvd_prod_of_mem (Nat.nth Nat.Prime) hi))

private lemma zero_mem_iff_two_dvd (A : Finset ℕ) : 0 ∈ A ↔ 2 ∣ primeProd A := by
  constructor
  · intro h
    rw [← Nat.nth_prime_zero_eq_two]
    exact dvd_prod_of_mem (Nat.nth Nat.Prime) h
  · intro h
    have h2 : 2 ∈ (primeProd A).primeFactors :=
      Nat.mem_primeFactors.2 ⟨Nat.prime_two, h, (primeProd_pos A).ne'⟩
    rw [primeFactors_primeProd] at h2
    obtain ⟨i, hi, hi2⟩ := mem_image.1 h2
    rw [← Nat.nth_prime_zero_eq_two] at hi2
    rwa [nth_prime_injective hi2] at hi

/-- The sets of prime indices whose products are at most $N$, that is, the squarefree numbers in
$\{1, \dots, N\}$. -/
private noncomputable def primeFamily (N : ℕ) : Finset (Finset ℕ) :=
  (range N).powerset.filter fun A => primeProd A ≤ N

private lemma mem_primeFamily {N : ℕ} {A : Finset ℕ} : A ∈ primeFamily N ↔ primeProd A ≤ N := by
  rw [primeFamily, mem_filter, mem_powerset]
  refine ⟨And.right, fun h => ⟨fun i hi => mem_range.2 ?_, h⟩⟩
  have := add_two_le_primeProd hi
  omega

private lemma isLowerSet_primeFamily (N : ℕ) :
    IsLowerSet ((primeFamily N : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
  intro A B hBA hA
  rw [mem_coe, mem_primeFamily] at hA ⊢
  exact (primeProd_le_of_subset hBA).trans hA

private lemma shift_primeFamily (N : ℕ) :
    ∀ A ∈ primeFamily N, ∀ j ∈ A, ∀ i < j, i ∉ A →
      insert i (A.erase j) ∈ primeFamily N := by
  intro A hA j hj i hij hiA
  rw [mem_primeFamily] at hA ⊢
  exact (primeProd_shift_le hj hij hiA).trans hA

/-- A set of squarefree numbers in $\{1, \dots, N\}$ with no squarefree pairwise product has at
most as many elements as the even squarefree numbers in $\{1, \dots, N\}$. -/
private lemma card_le_card_even_squarefree {N : ℕ} {T : Finset ℕ} (hT : T ⊆ Icc 1 N)
    (hsq : ∀ a ∈ T, Squarefree a) (hpair : ∀ a ∈ T, ∀ b ∈ T, ¬ Squarefree (a * b)) :
    #T ≤ #((evenOrOddNonSquarefree N).filter Squarefree) := by
  have hinj : Set.InjOn primeIdx T := fun a ha b hb h => by
    rw [← primeProd_primeIdx (hsq a ha), ← primeProd_primeIdx (hsq b hb), h]
  have hsub : T.image primeIdx ⊆ primeFamily N := by
    intro A hA
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hA
    rw [mem_primeFamily, primeProd_primeIdx (hsq a ha)]
    exact (mem_Icc.1 (hT ha)).2
  have hint : ((T.image primeIdx : Finset (Finset ℕ)) : Set (Finset ℕ)).Intersecting := by
    intro A hA B hB hAB
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hA
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hB
    apply hpair a ha b hb
    have h := squarefree_primeProd (primeIdx a ∪ primeIdx b)
    rwa [primeProd, prod_union hAB, ← primeProd, ← primeProd, primeProd_primeIdx (hsq a ha),
      primeProd_primeIdx (hsq b hb)] at h
  calc #T = #(T.image primeIdx) := (Finset.card_image_of_injOn hinj).symm
    _ ≤ #{A ∈ primeFamily N | 0 ∈ A} :=
      card_le_card_filter_zero_mem (isLowerSet_primeFamily N) (shift_primeFamily N) hsub hint
    _ ≤ #((evenOrOddNonSquarefree N).filter Squarefree) := by
      refine card_le_card_of_injOn primeProd (fun A hA => ?_) fun A _ B _ h => ?_
      · obtain ⟨hA, h0⟩ := mem_filter.1 (mem_coe.1 hA)
        rw [mem_primeFamily] at hA
        rw [mem_coe, mem_filter, evenOrOddNonSquarefree, mem_filter, mem_Icc]
        exact ⟨⟨⟨primeProd_pos A, hA⟩, Or.inl ((zero_mem_iff_two_dvd A).1 h0)⟩,
          squarefree_primeProd A⟩
      · rw [← primeIdx_primeProd A, ← primeIdx_primeProd B, h]

end PrimeIndices

/--
**Erdős Problem 844 is true.** For every natural number $N$, the largest size of a set
$A \subseteq \{1, \dots, N\}$ such that $ab$ is not squarefree for all $a, b \in A$ (including
$a = b$) is the number of integers $n$ with $1 \le n \le N$ that are even or not squarefree.

Source: B. Alexeev, D.
Mixon, and W. Sawin, The independence and clique cover numbers of the squarefree graph,
arXiv:2507.01928 (2025), https://arxiv.org/abs/2507.01928; Erdős Problems, Problem 844
(including Desmond Weisenberg's proof), https://www.erdosproblems.com/latex/844. Moved from
`OpenConjectures/NumberTheory/ErdosProblem844`.
-/
public theorem conjecture_holds : conjecture := by
  intro N
  refine ⟨⟨evenOrOddNonSquarefree N, filter_subset _ _, fun a ha b hb hab => ?_, rfl⟩, ?_⟩
  · rw [evenOrOddNonSquarefree, mem_filter] at ha hb
    rcases ha.2 with ha2 | ha2
    · rcases hb.2 with hb2 | hb2
      · obtain ⟨x, rfl⟩ := ha2
        obtain ⟨y, rfl⟩ := hb2
        have h := hab 2 ⟨x * y, by ring⟩
        exact absurd (Nat.isUnit_iff.1 h) (by norm_num)
      · exact hb2 hab.of_mul_right
    · exact ha2 hab.of_mul_left
  · rintro k ⟨A, hA, hpair, rfl⟩
    calc #A = #(A.filter Squarefree) + #(A.filter fun n => ¬ Squarefree n) :=
          (card_filter_add_card_filter_not _).symm
      _ ≤ #((evenOrOddNonSquarefree N).filter Squarefree) +
          #((evenOrOddNonSquarefree N).filter fun n => ¬ Squarefree n) := by
        refine add_le_add (card_le_card_even_squarefree ((filter_subset _ _).trans hA)
          (fun a ha => (mem_filter.1 ha).2)
          fun a ha b hb => hpair a (mem_filter.1 ha).1 b (mem_filter.1 hb).1) ?_
        refine card_le_card fun n hn => ?_
        obtain ⟨hn, hsq⟩ := mem_filter.1 hn
        rw [mem_filter, evenOrOddNonSquarefree, mem_filter]
        exact ⟨⟨hA hn, Or.inr hsq⟩, hsq⟩
      _ = #(evenOrOddNonSquarefree N) := card_filter_add_card_filter_not _

end MathlibExt.NumberTheory.ErdosProblem844Wanted
