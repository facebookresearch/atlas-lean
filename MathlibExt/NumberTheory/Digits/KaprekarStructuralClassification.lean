/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push

@[expose] public section

section
namespace MetaMathlibExt

private def kapFun (B : ℕ) (d : ℕ × ℕ) : ℕ × ℕ :=
  match List.insertionSort (· ≥ ·)
    (if d.2 = 0 then [d.1 - 1, B - 1, B - 1, B - d.1]
      else [d.1, d.2 - 1, B - d.2 - 1, B - d.1]) with
  | [a, b, c, e] => (a - e, b - c)
  | _ => (0, 0)

/-- Step 0: a descending-sorted permutation of a 4-list is the insertion sort. -/
private theorem sort_desc_of_perm {a b c e : ℕ} {l : List ℕ}
    (hperm : [a, b, c, e].Perm l) (hab : a ≥ b) (hbc : b ≥ c) (hce : c ≥ e) :
    List.insertionSort (· ≥ ·) l = [a, b, c, e] := by
  have h1 : (List.insertionSort (· ≥ ·) l).SortedGE := List.sortedGE_insertionSort
  have h2 : [a, b, c, e].SortedGE := by
    apply List.Pairwise.sortedGE
    rw [List.pairwise_iff_get]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> omega
  have hperm2 : (List.insertionSort (· ≥ ·) l).Perm [a, b, c, e] :=
    (List.perm_insertionSort _ l).trans hperm.symm
  exact List.Perm.eq_of_sortedGE h1 h2 hperm2

/-- Adjacent-swap permutations of 4-lists (proof-oriented). -/
private theorem perm01 (x y z w : ℕ) : [x, y, z, w].Perm [y, x, z, w] :=
  (List.Perm.swap x y [z, w]).symm
private theorem perm12 (x y z w : ℕ) : [x, y, z, w].Perm [x, z, y, w] :=
  (List.Perm.cons x (List.Perm.swap y z [w])).symm
private theorem perm23 (x y z w : ℕ) : [x, y, z, w].Perm [x, y, w, z] :=
  (List.Perm.cons x (List.Perm.cons y (List.Perm.swap z w []))).symm

/-- Evaluate kapFun once the sorted list is known. -/
private theorem kapFun_of_sort (B d1 d2 a b c e : ℕ)
    (hs : List.insertionSort (· ≥ ·)
      (if d2 = 0 then [d1 - 1, B - 1, B - 1, B - d1]
        else [d1, d2 - 1, B - d2 - 1, B - d1]) = [a, b, c, e]) :
    kapFun B (d1, d2) = (a - e, b - c) := by
  unfold kapFun
  change (match List.insertionSort (· ≥ ·)
    (if d2 = 0 then [d1 - 1, B - 1, B - 1, B - d1]
      else [d1, d2 - 1, B - d2 - 1, B - d1]) with
    | [a, b, c, e] => (a - e, b - c)
    | _ => (0, 0)) = _
  rw [hs]

/-- Step 1(i): closed form on the d2 = 0 face. -/
private theorem kapFun_zero {B d1 : ℕ} (h1 : 1 ≤ d1) (hB1 : d1 < B) :
    kapFun B (d1, 0) = (max (d1 - 1) (B - d1), min (d1 - 1) (B - d1)) := by
  by_cases h : d1 - 1 ≥ B - d1
  · have hsort : List.insertionSort (· ≥ ·) [d1 - 1, B - 1, B - 1, B - d1]
        = [B - 1, B - 1, d1 - 1, B - d1] :=
      sort_desc_of_perm
        ((perm12 _ _ _ _).trans (perm01 _ _ _ _)) (by omega) (by omega) h
    have hk := kapFun_of_sort B d1 0 (B - 1) (B - 1) (d1 - 1) (B - d1)
      (by simpa using hsort)
    rw [max_eq_left h, min_eq_right h, hk, Prod.mk.injEq]
    exact ⟨by omega, by omega⟩
  · have h' : B - d1 ≥ d1 - 1 := by omega
    have hsort : List.insertionSort (· ≥ ·) [d1 - 1, B - 1, B - 1, B - d1]
        = [B - 1, B - 1, B - d1, d1 - 1] :=
      sort_desc_of_perm
        ((perm23 _ _ _ _).trans ((perm12 _ _ _ _).trans (perm01 _ _ _ _)))
        (by omega) (by omega) h'
    have hk := kapFun_of_sort B d1 0 (B - 1) (B - 1) (B - d1) (d1 - 1)
      (by simpa using hsort)
    have hle : d1 - 1 ≤ B - d1 := by omega
    rw [max_eq_right hle, min_eq_left hle, hk, Prod.mk.injEq]
    exact ⟨by omega, by omega⟩

/-- Step 1(ii): closed form when d2 ≥ 1 and S ≠ T. -/
private theorem kapFun_ne_of_ne {B d1 d2 S T : ℕ} (hB : Odd B)
    (hS : S = if 2 * d1 ≥ B then 2 * d1 - B else B - 2 * d1)
    (hT : T = if 2 * d2 ≥ B then 2 * d2 - B else B - 2 * d2)
    (_h1 : 1 ≤ d1) (hB1 : d1 < B) (h2 : d2 ≤ d1) (hd2 : 1 ≤ d2)
    (hne : S ≠ T) :
    kapFun B (d1, d2) = (max S T, min S T) := by
  obtain ⟨k, hk⟩ := hB
  have hSodd : Odd S := by
    by_cases h : 2 * d1 ≥ B
    · have eS : S = 2 * d1 - B := by simp only [hS, h, ite_true]
      have h2d : 2 * d1 - B = 2 * (d1 - k - 1) + 1 := by omega
      rw [eS, h2d]; exact ⟨_, rfl⟩
    · have eS : S = B - 2 * d1 := by simp only [hS, h, ite_false]
      have h2d : B - 2 * d1 = 2 * (k - d1) + 1 := by omega
      rw [eS, h2d]; exact ⟨_, rfl⟩
  have hTodd : Odd T := by
    by_cases h : 2 * d2 ≥ B
    · have eT : T = 2 * d2 - B := by simp only [hT, h, ite_true]
      have h2d : 2 * d2 - B = 2 * (d2 - k - 1) + 1 := by omega
      rw [eT, h2d]; exact ⟨_, rfl⟩
    · have eT : T = B - 2 * d2 := by simp only [hT, h, ite_false]
      have h2d : B - 2 * d2 = 2 * (k - d2) + 1 := by omega
      rw [eT, h2d]; exact ⟨_, rfl⟩
  have h3 : S ≥ T + 2 ∨ T ≥ S + 2 := by
    obtain ⟨a, ha⟩ := hSodd; obtain ⟨b, hb⟩ := hTodd; omega
  have hne0 : d2 ≠ 0 := by omega
  by_cases hA : 2 * d1 ≥ B
  · by_cases hC : 2 * d2 ≥ B
    · have eS : S = 2 * d1 - B := by simp only [hS, hA, ite_true]
      have eT : T = 2 * d2 - B := by simp only [hT, hC, ite_true]
      subst eS; subst eT; clear hS hT hne hSodd hTodd
      rcases h3 with hST | hST
      · have hsort : List.insertionSort (· ≥ ·) [d1, d2 - 1, B - d2 - 1, B - d1]
            = [d1, d2 - 1, B - d2 - 1, B - d1] :=
          sort_desc_of_perm List.Perm.rfl (by omega) (by omega) (by omega)
        have hK := kapFun_of_sort B d1 d2 d1 (d2 - 1) (B - d2 - 1) (B - d1)
          (by simp only [hne0, ite_false]; exact hsort)
        rw [hK, max_eq_left (by omega), min_eq_right (by omega), Prod.mk.injEq]
        exact ⟨by omega, by omega⟩
      · have hsort : List.insertionSort (· ≥ ·) [d1, d2 - 1, B - d2 - 1, B - d1]
            = [d2 - 1, d1, B - d1, B - d2 - 1] :=
          sort_desc_of_perm ((perm01 _ _ _ _).trans (perm23 _ _ _ _))
            (by omega) (by omega) (by omega)
        have hK := kapFun_of_sort B d1 d2 (d2 - 1) d1 (B - d1) (B - d2 - 1)
          (by simp only [hne0, ite_false]; exact hsort)
        rw [hK, max_eq_right (by omega), min_eq_left (by omega), Prod.mk.injEq]
        exact ⟨by omega, by omega⟩
    · have eS : S = 2 * d1 - B := by simp only [hS, hA, ite_true]
      have eT : T = B - 2 * d2 := by simp only [hT, hC, ite_false]
      subst eS; subst eT; clear hS hT hne hSodd hTodd
      rcases h3 with hST | hST
      · have hsort : List.insertionSort (· ≥ ·) [d1, d2 - 1, B - d2 - 1, B - d1]
            = [d1, B - d2 - 1, d2 - 1, B - d1] :=
          sort_desc_of_perm (perm12 _ _ _ _)
            (by omega) (by omega) (by omega)
        have hK := kapFun_of_sort B d1 d2 d1 (B - d2 - 1) (d2 - 1) (B - d1)
          (by simp only [hne0, ite_false]; exact hsort)
        rw [hK, max_eq_left (by omega), min_eq_right (by omega), Prod.mk.injEq]
        exact ⟨by omega, by omega⟩
      · have hsort : List.insertionSort (· ≥ ·) [d1, d2 - 1, B - d2 - 1, B - d1]
            = [B - d2 - 1, d1, B - d1, d2 - 1] :=
          sort_desc_of_perm
            ((perm01 _ _ _ _).trans ((perm23 _ _ _ _).trans (perm12 _ _ _ _)))
            (by omega) (by omega) (by omega)
        have hK := kapFun_of_sort B d1 d2 (B - d2 - 1) d1 (B - d1) (d2 - 1)
          (by simp only [hne0, ite_false]; exact hsort)
        rw [hK, max_eq_right (by omega), min_eq_left (by omega), Prod.mk.injEq]
        exact ⟨by omega, by omega⟩
  · by_cases hC : 2 * d2 ≥ B
    · have eS : S = B - 2 * d1 := by simp only [hS, hA, ite_false]
      have eT : T = 2 * d2 - B := by simp only [hT, hC, ite_true]
      subst eS; subst eT; clear hS hT hne hSodd hTodd
      rcases h3 with hST | hST
      · have hsort : List.insertionSort (· ≥ ·) [d1, d2 - 1, B - d2 - 1, B - d1]
            = [B - d1, d2 - 1, B - d2 - 1, d1] :=
          sort_desc_of_perm
            ((perm01 _ _ _ _).trans ((perm12 _ _ _ _).trans ((perm23 _ _ _ _).trans
              ((perm12 _ _ _ _).trans (perm01 _ _ _ _)))))
            (by omega) (by omega) (by omega)
        have hK := kapFun_of_sort B d1 d2 (B - d1) (d2 - 1) (B - d2 - 1) d1
          (by simp only [hne0, ite_false]; exact hsort)
        rw [hK, max_eq_left (by omega), min_eq_right (by omega), Prod.mk.injEq]
        exact ⟨by omega, by omega⟩
      · have hsort : List.insertionSort (· ≥ ·) [d1, d2 - 1, B - d2 - 1, B - d1]
            = [d2 - 1, B - d1, d1, B - d2 - 1] :=
          sort_desc_of_perm
            ((perm12 _ _ _ _).trans ((perm23 _ _ _ _).trans (perm01 _ _ _ _)))
            (by omega) (by omega) (by omega)
        have hK := kapFun_of_sort B d1 d2 (d2 - 1) (B - d1) d1 (B - d2 - 1)
          (by simp only [hne0, ite_false]; exact hsort)
        rw [hK, max_eq_right (by omega), min_eq_left (by omega), Prod.mk.injEq]
        exact ⟨by omega, by omega⟩
    · have eS : S = B - 2 * d1 := by simp only [hS, hA, ite_false]
      have eT : T = B - 2 * d2 := by simp only [hT, hC, ite_false]
      subst eS; subst eT; clear hS hT hne hSodd hTodd
      rcases h3 with hST | hST
      · have hsort : List.insertionSort (· ≥ ·) [d1, d2 - 1, B - d2 - 1, B - d1]
            = [B - d1, B - d2 - 1, d2 - 1, d1] :=
          sort_desc_of_perm
            ((perm23 _ _ _ _).trans ((perm12 _ _ _ _).trans ((perm01 _ _ _ _).trans
              ((perm23 _ _ _ _).trans ((perm12 _ _ _ _).trans (perm23 _ _ _ _))))))
            (by omega) (by omega) (by omega)
        have hK := kapFun_of_sort B d1 d2 (B - d1) (B - d2 - 1) (d2 - 1) d1
          (by simp only [hne0, ite_false]; exact hsort)
        rw [hK, max_eq_left (by omega), min_eq_right (by omega), Prod.mk.injEq]
        exact ⟨by omega, by omega⟩
      · have hsort : List.insertionSort (· ≥ ·) [d1, d2 - 1, B - d2 - 1, B - d1]
            = [B - d2 - 1, B - d1, d1, d2 - 1] :=
          sort_desc_of_perm
            ((perm01 _ _ _ _).trans ((perm12 _ _ _ _).trans ((perm01 _ _ _ _).trans
              ((perm23 _ _ _ _).trans ((perm12 _ _ _ _).trans (perm23 _ _ _ _))))))
            (by omega) (by omega) (by omega)
        have hK := kapFun_of_sort B d1 d2 (B - d2 - 1) (B - d1) d1 (d2 - 1)
          (by simp only [hne0, ite_false]; exact hsort)
        rw [hK, max_eq_right (by omega), min_eq_left (by omega), Prod.mk.injEq]
        exact ⟨by omega, by omega⟩

/-- Step 1(iii): closed form when d2 ≥ 1 and S = T. -/
private theorem kapFun_of_seq {B d1 d2 S T : ℕ} (hB : Odd B)
    (hS : S = if 2 * d1 ≥ B then 2 * d1 - B else B - 2 * d1)
    (hT : T = if 2 * d2 ≥ B then 2 * d2 - B else B - 2 * d2)
    (_h1 : 1 ≤ d1) (hB1 : d1 < B) (h2 : d2 ≤ d1) (hd2 : 1 ≤ d2)
    (heq : S = T) :
    kapFun B (d1, d2) = (S + 1, S - 1) := by
  obtain ⟨k, hk⟩ := hB
  have hS1 : 1 ≤ S := by
    by_cases h : 2 * d1 ≥ B
    · have eS : S = 2 * d1 - B := by simp only [hS, h, ite_true]
      omega
    · have eS : S = B - 2 * d1 := by simp only [hS, h, ite_false]
      omega
  have hne0 : d2 ≠ 0 := by omega
  by_cases hA : 2 * d1 ≥ B
  · by_cases hC : 2 * d2 ≥ B
    · have eS : S = 2 * d1 - B := by simp only [hS, hA, ite_true]
      have eT : T = 2 * d2 - B := by simp only [hT, hC, ite_true]
      subst eS; subst eT; clear hS hT hS1
      have hsort : List.insertionSort (· ≥ ·) [d1, d2 - 1, B - d2 - 1, B - d1]
            = [d1, d2 - 1, B - d1, B - d2 - 1] :=
        sort_desc_of_perm (perm23 _ _ _ _)
          (by omega) (by omega) (by omega)
      have hK := kapFun_of_sort B d1 d2 d1 (d2 - 1) (B - d1) (B - d2 - 1)
        (by simp only [hne0, ite_false]; exact hsort)
      rw [hK, Prod.mk.injEq]
      exact ⟨by omega, by omega⟩
    · have eS : S = 2 * d1 - B := by simp only [hS, hA, ite_true]
      have eT : T = B - 2 * d2 := by simp only [hT, hC, ite_false]
      subst eS; subst eT; clear hS hT hS1
      have hsort : List.insertionSort (· ≥ ·) [d1, d2 - 1, B - d2 - 1, B - d1]
            = [d1, B - d2 - 1, B - d1, d2 - 1] :=
        sort_desc_of_perm ((perm23 _ _ _ _).trans (perm12 _ _ _ _))
          (by omega) (by omega) (by omega)
      have hK := kapFun_of_sort B d1 d2 d1 (B - d2 - 1) (B - d1) (d2 - 1)
        (by simp only [hne0, ite_false]; exact hsort)
      rw [hK, Prod.mk.injEq]
      exact ⟨by omega, by omega⟩
  · by_cases hC : 2 * d2 ≥ B
    · have eS : S = B - 2 * d1 := by simp only [hS, hA, ite_false]
      have eT : T = 2 * d2 - B := by simp only [hT, hC, ite_true]
      subst eS; subst eT; clear hS hT hS1
      have hsort : List.insertionSort (· ≥ ·) [d1, d2 - 1, B - d2 - 1, B - d1]
            = [B - d1, d2 - 1, d1, B - d2 - 1] :=
        sort_desc_of_perm
          ((perm01 _ _ _ _).trans ((perm12 _ _ _ _).trans
            ((perm23 _ _ _ _).trans (perm01 _ _ _ _))))
          (by omega) (by omega) (by omega)
      have hK := kapFun_of_sort B d1 d2 (B - d1) (d2 - 1) d1 (B - d2 - 1)
        (by simp only [hne0, ite_false]; exact hsort)
      rw [hK, Prod.mk.injEq]
      exact ⟨by omega, by omega⟩
    · have eS : S = B - 2 * d1 := by simp only [hS, hA, ite_false]
      have eT : T = B - 2 * d2 := by simp only [hT, hC, ite_false]
      subst eS; subst eT; clear hS hT hS1
      have hsort : List.insertionSort (· ≥ ·) [d1, d2 - 1, B - d2 - 1, B - d1]
            = [B - d1, B - d2 - 1, d1, d2 - 1] :=
        sort_desc_of_perm
          ((perm12 _ _ _ _).trans ((perm01 _ _ _ _).trans
            ((perm23 _ _ _ _).trans ((perm12 _ _ _ _).trans (perm23 _ _ _ _)))))
          (by omega) (by omega) (by omega)
      have hK := kapFun_of_sort B d1 d2 (B - d1) (B - d2 - 1) d1 (d2 - 1)
        (by simp only [hne0, ite_false]; exact hsort)
      rw [hK, Prod.mk.injEq]
      exact ⟨by omega, by omega⟩

private def XBset (B : ℕ) : Set (ℕ × ℕ) := {d | 1 ≤ d.1 ∧ d.1 < B ∧ d.2 ≤ d.1}
private def TBset (B : ℕ) : Set (ℕ × ℕ) :=
  {d | d ∈ XBset B ∧ d.2 < d.1 ∧ 0 < d.2 ∧ Odd d.1 ∧ Odd d.2}

private theorem iterate3_eq {α : Type*} (f : α → α) (x : α) : f^[3] x = f (f (f x)) := rfl

/-- S = |2d - B| is odd, positive, and below B. -/
private theorem absdiff_mem {B d S : ℕ} (hB : Odd B)
    (hS : S = if 2 * d ≥ B then 2 * d - B else B - 2 * d)
    (h1 : 1 ≤ d) (hB1 : d < B) : Odd S ∧ 1 ≤ S ∧ S < B := by
  obtain ⟨k, hk⟩ := hB
  by_cases h : 2 * d ≥ B
  · have eS : S = 2 * d - B := by simp only [hS, h, ite_true]
    subst eS
    have h2d : 2 * d - B = 2 * (d - k - 1) + 1 := by omega
    refine ⟨by rw [h2d]; exact ⟨_, rfl⟩, by omega, by omega⟩
  · have eS : S = B - 2 * d := by simp only [hS, h, ite_false]
    subst eS
    have h2d : B - 2 * d = 2 * (k - d) + 1 := by omega
    refine ⟨by rw [h2d]; exact ⟨_, rfl⟩, by omega, by omega⟩

/-- S = T when d1 = d2 or d1 + d2 = B. -/
private theorem ST_eq_of {B d1 d2 S T : ℕ} (hB : Odd B)
    (hS : S = if 2 * d1 ≥ B then 2 * d1 - B else B - 2 * d1)
    (hT : T = if 2 * d2 ≥ B then 2 * d2 - B else B - 2 * d2)
    (h : d1 = d2 ∨ d1 + d2 = B) : S = T := by
  obtain ⟨k, hk⟩ := hB
  rcases h with rfl | hsum
  · rw [hS, hT]
  · by_cases hA : 2 * d1 ≥ B <;> by_cases hC : 2 * d2 ≥ B
    · simp only [hS, hT, hA, hC, ite_true]; omega
    · simp only [hS, hT, hA, hC, ite_true, ite_false]; omega
    · simp only [hS, hT, hA, hC, ite_false, ite_true]; omega
    · simp only [hS, hT, hA, hC, ite_false]; omega

/-- Good lemma (S ≠ T form): K d lands in T. -/
private theorem kap_mem_T_of_STne {B d1 d2 S T : ℕ} (hB : Odd B)
    (hS : S = if 2 * d1 ≥ B then 2 * d1 - B else B - 2 * d1)
    (hT : T = if 2 * d2 ≥ B then 2 * d2 - B else B - 2 * d2)
    (h1 : 1 ≤ d1) (hB1 : d1 < B) (h2 : d2 ≤ d1) (hd2 : 1 ≤ d2)
    (hST : S ≠ T) :
    kapFun B (d1, d2) ∈ TBset B := by
  have h2B : d2 < B := by omega
  obtain ⟨hSodd, hS1, hSB⟩ := absdiff_mem hB hS h1 hB1
  obtain ⟨hTodd, hT1, hTB⟩ := absdiff_mem hB hT hd2 h2B
  have hK : kapFun B (d1, d2) = (max S T, min S T) :=
    kapFun_ne_of_ne hB hS hT h1 hB1 h2 hd2 hST
  rw [hK]
  have hmax1 : 1 ≤ max S T := by
    by_cases hle : S ≤ T
    · rw [max_eq_right hle]; exact hT1
    · rw [max_eq_left (by omega : T ≤ S)]; exact hS1
  have hmaxB : max S T < B := by
    by_cases hle : S ≤ T
    · rw [max_eq_right hle]; exact hTB
    · rw [max_eq_left (by omega : T ≤ S)]; exact hSB
  have hminmax : min S T ≤ max S T :=
    le_trans (min_le_left _ _) (le_max_left _ _)
  have hminlt : min S T < max S T := by
    by_cases hle : S ≤ T
    · rw [min_eq_left hle, max_eq_right hle]
      exact lt_of_le_of_ne hle hST
    · have hle' : T ≤ S := by omega
      rw [min_eq_right hle', max_eq_left hle']
      exact lt_of_le_of_ne hle' (Ne.symm hST)
  have hmin1 : 1 ≤ min S T := by
    by_cases hle : S ≤ T
    · rw [min_eq_left hle]; exact hS1
    · rw [min_eq_right (by omega : T ≤ S)]; exact hT1
  have hmaxodd : Odd (max S T) := by
    by_cases hle : S ≤ T
    · rw [max_eq_right hle]; exact hTodd
    · rw [max_eq_left (by omega : T ≤ S)]; exact hSodd
  have hminodd : Odd (min S T) := by
    by_cases hle : S ≤ T
    · rw [min_eq_left hle]; exact hSodd
    · rw [min_eq_right (by omega : T ≤ S)]; exact hTodd
  refine ⟨⟨hmax1, hmaxB, hminmax⟩, hminlt, hmin1, hmaxodd, hminodd⟩

/-- Good lemma (pair form): K d lands in T. -/
private theorem kap_mem_T_of_ne {B d1 d2 : ℕ} (hB : Odd B)
    (h1 : 1 ≤ d1) (hB1 : d1 < B) (h2 : d2 ≤ d1) (hd2 : 1 ≤ d2)
    (hne12 : d1 ≠ d2) (hnesum : d1 + d2 ≠ B) :
    kapFun B (d1, d2) ∈ TBset B := by
  have hST : (if 2 * d1 ≥ B then 2 * d1 - B else B - 2 * d1) ≠
      (if 2 * d2 ≥ B then 2 * d2 - B else B - 2 * d2) := by
    intro heq
    by_cases hA : 2 * d1 ≥ B <;> by_cases hC : 2 * d2 ≥ B
    · simp only [hA, hC, ite_true] at heq; omega
    · simp only [hA, hC, ite_true, ite_false] at heq; omega
    · simp only [hA, hC, ite_false, ite_true] at heq; omega
    · simp only [hA, hC, ite_false] at heq; omega
  exact kap_mem_T_of_STne hB rfl rfl h1 hB1 h2 hd2 hST

/-- Step 2 (conjunct 1): K maps T to T. -/
private theorem kap_maps_T (B : ℕ) (hB : Odd B) (_hB3 : 3 < B) :
    Set.MapsTo (kapFun B) (TBset B) (TBset B) := by
  intro d hd
  simp only [TBset, XBset, Set.mem_ofPred_eq] at hd
  obtain ⟨⟨h1, hB1, h2⟩, hlt, hpos, hodd1, hodd2⟩ := hd
  have hne12 : d.1 ≠ d.2 := ne_of_gt hlt
  have hnesum : d.1 + d.2 ≠ B := by
    obtain ⟨a, ha⟩ := hodd1; obtain ⟨b, hb⟩ := hodd2; obtain ⟨c, hc⟩ := hB
    omega
  have h2' : d.2 ≤ d.1 := le_of_lt hlt
  have hd2 : 1 ≤ d.2 := hpos
  exact kap_mem_T_of_ne hB h1 hB1 h2' hd2 hne12 hnesum

private theorem kap_pt1 {B : ℕ} (hB3 : 3 < B) : kapFun B (2, 0) = (B - 2, 1) := by
  have h : kapFun B (2, 0) = (max (2 - 1) (B - 2), min (2 - 1) (B - 2)) :=
    kapFun_zero (by omega) (by omega)
  have e1 : (2 : ℕ) - 1 = 1 := by decide
  rw [e1, max_eq_right (by omega : (1 : ℕ) ≤ B - 2),
    min_eq_left (by omega : (1 : ℕ) ≤ B - 2)] at h
  exact h

private theorem kap_pt2 {B : ℕ} (hB3 : 3 < B) : kapFun B (B - 1, 0) = (B - 2, 1) := by
  have h : kapFun B (B - 1, 0) =
      (max (B - 1 - 1) (B - (B - 1)), min (B - 1 - 1) (B - (B - 1))) :=
    kapFun_zero (by omega) (by omega)
  have e1 : B - (B - 1) = 1 := by omega
  have e2 : B - 1 - 1 = B - 2 := by omega
  rw [e1, e2, max_eq_left (by omega : (1 : ℕ) ≤ B - 2),
    min_eq_right (by omega : (1 : ℕ) ≤ B - 2)] at h
  exact h

private theorem kap_pt3 {B : ℕ} (hB : Odd B) (hB3 : 3 < B) :
    kapFun B ((B - 1) / 2, (B - 1) / 2) = (2, 0) := by
  have ⟨c, hc⟩ := hB
  have hev : Even (B - 1) := ⟨c, by omega⟩
  have h2m : 2 * ((B - 1) / 2) = B - 1 := Nat.two_mul_div_two_of_even hev
  have hcond : ¬ (2 * ((B - 1) / 2) ≥ B) := by omega
  have hS : (1 : ℕ) = if 2 * ((B - 1) / 2) ≥ B then 2 * ((B - 1) / 2) - B
      else B - 2 * ((B - 1) / 2) := by
    simp only [hcond, ite_false]
    omega
  have hK := kapFun_of_seq hB hS hS (by omega) (by omega) (by omega) (by omega) rfl
  simpa using hK

private theorem hmemB21 {B : ℕ} (hB : Odd B) (hB3 : 3 < B) : (B - 2, 1) ∈ TBset B := by
  obtain ⟨c, hc⟩ := hB
  have hodd : Odd (B - 2) := by
    have e : B - 2 = 2 * (c - 1) + 1 := by omega
    rw [e]; exact ⟨_, rfl⟩
  refine ⟨⟨by omega, by omega, by omega⟩, by omega, by omega, hodd, ⟨0, rfl⟩⟩

/-- Step 3 (conjunct 2): K^3 maps X to T. -/
private theorem kap_iter3 (B : ℕ) (hB : Odd B) (hB3 : 3 < B) :
    Set.MapsTo ((kapFun B)^[3]) (XBset B) (TBset B) := by
  have hstab := kap_maps_T B hB hB3
  have hB21 := hmemB21 hB hB3
  intro d hd
  simp only [XBset, Set.mem_ofPred_eq] at hd
  obtain ⟨h1, hB1, h2⟩ := hd
  set S := if 2 * d.1 ≥ B then 2 * d.1 - B else B - 2 * d.1 with hSdef
  set T := if 2 * d.2 ≥ B then 2 * d.2 - B else B - 2 * d.2 with hTdef
  rw [iterate3_eq, show d = (d.1, d.2) from rfl]
  by_cases hd2 : d.2 = 0
  · have e : (d.1, d.2) = (d.1, 0) := by rw [hd2]
    rw [e]
    have hK0 : kapFun B (d.1, 0) =
        (max (d.1 - 1) (B - d.1), min (d.1 - 1) (B - d.1)) :=
      kapFun_zero h1 hB1
    rw [hK0]
    have hsum : max (d.1 - 1) (B - d.1) + min (d.1 - 1) (B - d.1) = B - 1 := by
      omega
    by_cases hy0 : min (d.1 - 1) (B - d.1) = 0
    · have hpair : (max (d.1 - 1) (B - d.1), min (d.1 - 1) (B - d.1))
          = (B - 1, 0) := by
        rw [Prod.mk.injEq]
        exact ⟨by omega, hy0⟩
      rw [hpair, kap_pt2 hB3]
      exact hstab hB21
    · by_cases hxy : max (d.1 - 1) (B - d.1) = min (d.1 - 1) (B - d.1)
      · have hxm : max (d.1 - 1) (B - d.1) = (B - 1) / 2 := by omega
        have hpair : (max (d.1 - 1) (B - d.1), min (d.1 - 1) (B - d.1)) =
            ((B - 1) / 2, (B - 1) / 2) := by
          rw [Prod.mk.injEq]
          exact ⟨hxm, by omega⟩
        rw [hpair, kap_pt3 hB hB3, kap_pt1 hB3]
        exact hB21
      · have h2T : kapFun B (max (d.1 - 1) (B - d.1),
            min (d.1 - 1) (B - d.1)) ∈ TBset B := by
          apply kap_mem_T_of_ne hB
          · omega
          · omega
          · omega
          · omega
          · exact hxy
          · omega
        exact hstab h2T
  · have hd2' : 1 ≤ d.2 := by omega
    by_cases hST : S = T
    · obtain ⟨hSodd, hS1, hSB⟩ := absdiff_mem hB hSdef h1 hB1
      have hK1 : kapFun B (d.1, d.2) = (S + 1, S - 1) :=
        kapFun_of_seq hB hSdef hTdef h1 hB1 h2 hd2' hST
      by_cases hSeq1 : S = 1
      · rw [hSeq1] at hK1
        have e20 : ((1 : ℕ) + 1, (1 : ℕ) - 1) = (2, 0) := by decide
        rw [hK1, e20, kap_pt1 hB3]
        exact hstab hB21
      · have hS3 : 3 ≤ S := by
          obtain ⟨a, ha⟩ := hSodd; omega
        have ⟨k, hk⟩ := hB
        have ⟨a, ha⟩ := hSodd
        have h2T : kapFun B (S + 1, S - 1) ∈ TBset B := by
          apply kap_mem_T_of_ne hB <;> omega
        rw [hK1]
        exact hstab h2T
    · have h1T : kapFun B (d.1, d.2) ∈ TBset B :=
        kap_mem_T_of_STne hB hSdef hTdef h1 hB1 h2 hd2' hST
      have h2T : kapFun B (kapFun B (d.1, d.2)) ∈ TBset B := hstab h1T
      exact hstab h2T

private def dblFun (B : ℕ) (S : Finset (Finset (ZMod B))) : Finset (Finset (ZMod B)) :=
  S.image (fun C => C.image (· * 2))

private def ProjSet (B : ℕ) : Set (Finset (Finset (ZMod B))) :=
  {S | S.card = 2 ∧ ∀ C ∈ S, ∃ x : ZMod B, x ≠ 0 ∧ C = {x, -x}}

/-- Step 4 (conjunct 3): doubling preserves Proj. -/
private theorem dbl_preserves {B : ℕ} (hB : Odd B) {S : Finset (Finset (ZMod B))}
    (hS : S ∈ ProjSet B) : dblFun B S ∈ ProjSet B := by
  have hcop : Nat.Coprime 2 B := (Nat.coprime_two_left).mpr hB
  have hunit : IsUnit ((2 : ℕ) : ZMod B) := (ZMod.isUnit_iff_coprime 2 B).mpr hcop
  have hunit2 : IsUnit (2 : ZMod B) := by simpa using hunit
  have hinj : Function.Injective (fun x : ZMod B => x * 2) :=
    IsUnit.mul_left_injective hunit2
  have himj : Function.Injective (Finset.image (fun x : ZMod B => x * 2)) :=
    Finset.image_injective hinj
  simp only [ProjSet, Set.mem_ofPred_eq] at hS ⊢
  obtain ⟨hcard, hmem⟩ := hS
  rw [Finset.card_eq_two] at hcard
  obtain ⟨C1, C2, h12, rfl⟩ := hcard
  obtain ⟨x1, hx10, hx1⟩ := hmem C1 (by simp)
  obtain ⟨x2, hx20, hx2⟩ := hmem C2 (by simp)
  have himg1 : Finset.image (fun x : ZMod B => x * 2) C1
      = {x1 * 2, -(x1 * 2)} := by
    rw [hx1, Finset.image_insert, Finset.image_singleton, neg_mul]
  have himg2 : Finset.image (fun x : ZMod B => x * 2) C2
      = {x2 * 2, -(x2 * 2)} := by
    rw [hx2, Finset.image_insert, Finset.image_singleton, neg_mul]
  have hy10 : x1 * 2 ≠ 0 := by
    intro hz
    apply hx10
    apply hinj
    change x1 * 2 = 0 * 2
    rw [hz, zero_mul]
  have hy20 : x2 * 2 ≠ 0 := by
    intro hz
    apply hx20
    apply hinj
    change x2 * 2 = 0 * 2
    rw [hz, zero_mul]
  have h12' : Finset.image (fun x : ZMod B => x * 2) C1 ≠
      Finset.image (fun x : ZMod B => x * 2) C2 := himj.ne h12
  rw [himg1] at h12'
  rw [himg2] at h12'
  simp only [dblFun, Finset.image_insert, Finset.image_singleton, himg1, himg2]
  refine ⟨Finset.card_pair h12', ?_⟩
  intro C hC
  simp only [Finset.mem_insert, Finset.mem_singleton] at hC
  rcases hC with rfl | rfl
  · exact ⟨x1 * 2, hy10, rfl⟩
  · exact ⟨x2 * 2, hy20, rfl⟩

private theorem cast_ne_zero_of_lt {B a : ℕ} (ha0 : 0 < a) (haB : a < B) :
    (↑a : ZMod B) ≠ 0 := by
  intro hz
  have hdvd : B ∣ a := (ZMod.natCast_eq_zero_iff a B).mp hz
  have hle : B ≤ a := Nat.le_of_dvd ha0 hdvd
  omega

/-- Two classes {u,-u}, {v,-v} differ when 0 < v < u and u + v < B. -/
private theorem classes_ne {B u v : ℕ} (hv0 : 0 < v) (hvu : v < u) (hsum : u + v < B) :
    ({(↑u : ZMod B), -(↑u : ZMod B)} : Finset (ZMod B)) ≠
      ({(↑v : ZMod B), -(↑v : ZMod B)} : Finset (ZMod B)) := by
  have huB : u < B := by omega
  have hvB : v < B := by omega
  intro heq
  have hcoe : ({(↑u : ZMod B), -(↑u : ZMod B)} : Set (ZMod B)) =
      ({(↑v : ZMod B), -(↑v : ZMod B)} : Set (ZMod B)) := by
    have h2 := congrArg (fun s : Finset (ZMod B) => (s : Set (ZMod B))) heq
    simpa [Finset.coe_pair] using h2
  rw [Set.pair_eq_pair_iff] at hcoe
  rcases hcoe with ⟨h1, -⟩ | ⟨h1, -⟩
  · -- straight: ↑u = ↑v forces u = v
    have hmod : u % B = v % B := (ZMod.natCast_eq_natCast_iff' u v B).mp h1
    rw [Nat.mod_eq_of_lt huB, Nat.mod_eq_of_lt hvB] at hmod
    omega
  · -- crossed: ↑u = -↑v forces B ∣ u + v
    have hsum0 : (↑(u + v) : ZMod B) = 0 := by
      push_cast
      rw [h1, neg_add_cancel]
    have hdvd : B ∣ (u + v) := (ZMod.natCast_eq_zero_iff (u + v) B).mp hsum0
    have hle : B ≤ u + v := Nat.le_of_dvd (by omega) hdvd
    omega

/-- The pair of classes {{u,-u},{v,-v}} lies in Proj. -/
private theorem pair_mem_Proj {B u v : ℕ} (hv0 : 0 < v) (hvu : v < u) (hsum : u + v < B) :
    ({{(↑u : ZMod B), -(↑u : ZMod B)},
      ({(↑v : ZMod B), -(↑v : ZMod B)} : Finset (ZMod B))} :
      Finset (Finset (ZMod B))) ∈ ProjSet B := by
  simp only [ProjSet, Set.mem_ofPred_eq]
  refine ⟨Finset.card_pair (classes_ne hv0 hvu hsum), ?_⟩
  intro C hC
  simp only [Finset.mem_insert, Finset.mem_singleton] at hC
  rcases hC with rfl | rfl
  · exact ⟨_, cast_ne_zero_of_lt (by omega) (by omega), rfl⟩
  · exact ⟨_, cast_ne_zero_of_lt hv0 (by omega), rfl⟩

/-- Phi bundled as a top-level function (defeq to the lets Phi). -/
private def phiFun (B : ℕ) (d : ↥(TBset B)) : Finset (Finset (ZMod B)) :=
  {{(((d.1.1 + d.1.2) / 2 : ℕ) : ZMod B), -(((d.1.1 + d.1.2) / 2 : ℕ) : ZMod B)},
   ({(((d.1.1 - d.1.2) / 2 : ℕ) : ZMod B), -(((d.1.1 - d.1.2) / 2 : ℕ) : ZMod B)} :
    Finset (ZMod B))}

/-- Step 5 (conjunct 4): Phi d lies in Proj. -/
private theorem phi_mem_Proj {B : ℕ} (d : ↥(TBset B)) : phiFun B d ∈ ProjSet B := by
  have hprop : d.1 ∈ TBset B := d.property
  simp only [TBset, XBset, Set.mem_ofPred_eq] at hprop
  obtain ⟨⟨h1, hB1, h2⟩, hlt, hpos, hodd1, hodd2⟩ := hprop
  have hE1 : Even (d.1.1 + d.1.2) := Odd.add_odd hodd1 hodd2
  have hE2 : Even (d.1.1 - d.1.2) := Nat.Odd.sub_odd hodd1 hodd2
  have h2u : 2 * ((d.1.1 + d.1.2) / 2) = d.1.1 + d.1.2 :=
    Nat.two_mul_div_two_of_even hE1
  have h2v : 2 * ((d.1.1 - d.1.2) / 2) = d.1.1 - d.1.2 :=
    Nat.two_mul_div_two_of_even hE2
  have h2le : d.1.2 ≤ d.1.1 := le_of_lt hlt
  simp only [phiFun]
  apply pair_mem_Proj
  · omega
  · omega
  · omega

/-- Cast equality reflects naturals below B. -/
private theorem cast_eq_cast {B a b : ℕ} (haB : a < B) (hbB : b < B)
    (h : (↑a : ZMod B) = ↑b) : a = b := by
  have hmod : a % B = b % B := (ZMod.natCast_eq_natCast_iff' a b B).mp h
  rw [Nat.mod_eq_of_lt haB, Nat.mod_eq_of_lt hbB] at hmod
  exact hmod

/-- A cast negated: ↑a = -↑b with both positive and below B means a + b = B. -/
private theorem cast_eq_neg {B a b : ℕ} (ha0 : 0 < a) (haB : a < B)
    (hb0 : 0 < b) (hbB : b < B)
    (h : (↑a : ZMod B) = -↑b) : a + b = B := by
  have h0 : (↑(a + b) : ZMod B) = 0 := by
    push_cast
    rw [h, neg_add_cancel]
  have hdvd : B ∣ (a + b) := (ZMod.natCast_eq_zero_iff (a + b) B).mp h0
  have hle : B ≤ a + b := Nat.le_of_dvd (by omega) hdvd
  have hlt2 : a + b < 2 * B := by omega
  by_contra hne
  have hgt : B < a + b := lt_of_le_of_ne hle (Ne.symm hne)
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : 2 ≤ k := by
    by_contra hc
    push Not at hc
    interval_cases k
    · simp at hk
      omega
    · simp at hk
      omega
  have hge : 2 * B ≤ a + b := by
    have h1 : B * 2 ≤ B * k := Nat.mul_le_mul (le_refl B) hk2
    omega
  omega

/-- Equality of two nonzero classes reflects to naturals. -/
private theorem class_eq_nat {B a b : ℕ} (ha0 : 0 < a) (haB : a < B)
    (hb0 : 0 < b) (hbB : b < B)
    (h : ({(↑a : ZMod B), -(↑a : ZMod B)} : Finset (ZMod B)) =
      ({(↑b : ZMod B), -(↑b : ZMod B)} : Finset (ZMod B))) :
    a = b ∨ a + b = B := by
  have hcoe : ({(↑a : ZMod B), -(↑a : ZMod B)} : Set (ZMod B)) =
      ({(↑b : ZMod B), -(↑b : ZMod B)} : Set (ZMod B)) := by
    have h2 := congrArg (fun s : Finset (ZMod B) => (s : Set (ZMod B))) h
    simpa [Finset.coe_pair] using h2
  rw [Set.pair_eq_pair_iff] at hcoe
  rcases hcoe with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Or.inl (cast_eq_cast haB hbB h1)
  · exact Or.inr (cast_eq_neg ha0 haB hb0 hbB h1)

/-- Arithmetic facts for the u, v of a point in T. -/
private theorem uv_facts {B : ℕ} (d : ↥(TBset B)) :
    2 * ((d.1.1 + d.1.2) / 2) = d.1.1 + d.1.2 ∧
    2 * ((d.1.1 - d.1.2) / 2) = d.1.1 - d.1.2 ∧
    (d.1.1 + d.1.2) / 2 + (d.1.1 - d.1.2) / 2 = d.1.1 ∧
    d.1.2 = (d.1.1 + d.1.2) / 2 - (d.1.1 - d.1.2) / 2 ∧
    0 < (d.1.1 - d.1.2) / 2 ∧
    (d.1.1 - d.1.2) / 2 < (d.1.1 + d.1.2) / 2 ∧
    (d.1.1 + d.1.2) / 2 + (d.1.1 - d.1.2) / 2 < B ∧
    Odd ((d.1.1 + d.1.2) / 2 + (d.1.1 - d.1.2) / 2) := by
  have hprop : d.1 ∈ TBset B := d.property
  simp only [TBset, XBset, Set.mem_ofPred_eq] at hprop
  obtain ⟨⟨h1, hB1, h2⟩, hlt, hpos, hodd1, hodd2⟩ := hprop
  have hE1 : Even (d.1.1 + d.1.2) := Odd.add_odd hodd1 hodd2
  have hE2 : Even (d.1.1 - d.1.2) := Nat.Odd.sub_odd hodd1 hodd2
  have h2u : 2 * ((d.1.1 + d.1.2) / 2) = d.1.1 + d.1.2 :=
    Nat.two_mul_div_two_of_even hE1
  have h2v : 2 * ((d.1.1 - d.1.2) / 2) = d.1.1 - d.1.2 :=
    Nat.two_mul_div_two_of_even hE2
  have h2le : d.1.2 ≤ d.1.1 := le_of_lt hlt
  have huv : (d.1.1 + d.1.2) / 2 + (d.1.1 - d.1.2) / 2 = d.1.1 := by omega
  refine ⟨h2u, h2v, huv, by omega, by omega, by omega, by omega, ?_⟩
  rw [huv]
  exact hodd1

/-- Phi is injective. -/
private theorem phi_inj {B : ℕ} (hB : Odd B) {d d' : ↥(TBset B)}
    (h : phiFun B d = phiFun B d') : d = d' := by
  obtain ⟨h2u, h2v, huv, hd2, hv0, hvu, hsum, hodd⟩ := uv_facts d
  obtain ⟨h2u', h2v', huv', hd2', hv0', hvu', hsum', hodd'⟩ := uv_facts d'
  have huB : (d.1.1 + d.1.2) / 2 < B := by omega
  have hvB : (d.1.1 - d.1.2) / 2 < B := by omega
  have hu0 : 0 < (d.1.1 + d.1.2) / 2 := by omega
  have huB' : (d'.1.1 + d'.1.2) / 2 < B := by omega
  have hvB' : (d'.1.1 - d'.1.2) / 2 < B := by omega
  have hu0' : 0 < (d'.1.1 + d'.1.2) / 2 := by omega
  set u : ℕ := (d.1.1 + d.1.2) / 2 with hu
  set v : ℕ := (d.1.1 - d.1.2) / 2 with hv
  set u' : ℕ := (d'.1.1 + d'.1.2) / 2 with hu'
  set v' : ℕ := (d'.1.1 - d'.1.2) / 2 with hv'
  simp only [phiFun] at h
  have houter : ({{(↑u : ZMod B), -(↑u : ZMod B)},
      ({(↑v : ZMod B), -(↑v : ZMod B)} : Finset (ZMod B))} :
      Set (Finset (ZMod B))) =
      ({{(↑u' : ZMod B), -(↑u' : ZMod B)},
      ({(↑v' : ZMod B), -(↑v' : ZMod B)} : Finset (ZMod B))} :
      Set (Finset (ZMod B))) := by
    have h2 := congrArg (fun s : Finset (Finset (ZMod B)) => (s : Set (Finset (ZMod B)))) h
    simpa [Finset.coe_pair] using h2
  rw [Set.pair_eq_pair_iff] at houter
  have hU : ({(↑u : ZMod B), -(↑u : ZMod B)} : Finset (ZMod B)) =
      ({(↑u' : ZMod B), -(↑u' : ZMod B)} : Finset (ZMod B)) ∨
      ({(↑u : ZMod B), -(↑u : ZMod B)} : Finset (ZMod B)) =
      ({(↑v' : ZMod B), -(↑v' : ZMod B)} : Finset (ZMod B)) := by
    rcases houter with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hV : ({(↑v : ZMod B), -(↑v : ZMod B)} : Finset (ZMod B)) =
      ({(↑v' : ZMod B), -(↑v' : ZMod B)} : Finset (ZMod B)) ∨
      ({(↑v : ZMod B), -(↑v : ZMod B)} : Finset (ZMod B)) =
      ({(↑u' : ZMod B), -(↑u' : ZMod B)} : Finset (ZMod B)) := by
    rcases houter with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inl h2
    · exact Or.inr h2
  have hUUvv : u = u' ∧ v = v' := by
    rcases hU with hUu | hUv
    · -- straight on U
      rcases class_eq_nat hu0 huB hu0' huB' hUu with hUU | hUU
      · rcases hV with hVv | hVu
        · rcases class_eq_nat hv0 hvB hv0' hvB' hVv with hVV | hVV
          · exact ⟨hUU, hVV⟩
          · exfalso; omega
        · rcases class_eq_nat hv0 hvB hu0' huB' hVu with hVV | hVV
          · exfalso; omega
          · exfalso; omega
      · -- u + u' = B contradicts parity
        rcases hV with hVv | hVu
        · rcases class_eq_nat hv0 hvB hv0' hvB' hVv with hVV | hVV
          · have hE : Even ((u + v) + (u' + v')) := Odd.add_odd hodd hodd'
            have hT : (u + v) + (u' + v') = B + 2 * v := by omega
            have hO2 : Odd (B + 2 * v) := by
              obtain ⟨c, hc⟩ := hB
              exact ⟨c + v, by omega⟩
            obtain ⟨k, hk⟩ := hE
            obtain ⟨l, hl⟩ := hO2
            omega
          · exfalso; omega
        · exfalso
          rcases class_eq_nat hv0 hvB hu0' huB' hVu with hVV | hVV <;> omega
    · -- crossed: U = V'
      rcases class_eq_nat hu0 huB hv0' hvB' hUv with hUV | hUV
      · rcases hV with hVv | hVu
        · rcases class_eq_nat hv0 hvB hv0' hvB' hVv with hVV | hVV <;> omega
        · rcases class_eq_nat hv0 hvB hu0' huB' hVu with hVV | hVV <;> omega
      · rcases hV with hVv | hVu
        · rcases class_eq_nat hv0 hvB hv0' hvB' hVv with hVV | hVV <;> omega
        · rcases class_eq_nat hv0 hvB hu0' huB' hVu with hVV | hVV <;> omega
  obtain ⟨hUU, hVV⟩ := hUUvv
  apply Subtype.ext
  rw [Prod.ext_iff]
  constructor <;> omega

/-- Each nonzero class has a small representative q in [1, (B-1)/2]. -/
private theorem class_small_rep {B : ℕ} [NeZero B] (hB : Odd B) {x : ZMod B}
    (hx : x ≠ 0) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ (B - 1) / 2 ∧
      (((q : ℕ) : ZMod B) = x ∨ ((q : ℕ) : ZMod B) = -x) ∧
      (q = x.val ∨ q = B - x.val) := by
  have hrB : x.val < B := ZMod.val_lt x
  have hr0 : 0 < x.val := by
    by_contra hc
    push Not at hc
    interval_cases h : x.val
    · exact hx ((ZMod.val_eq_zero x).mp h)
  have e1 : ((x.val : ℕ) : ZMod B) = x := ZMod.natCast_zmod_val x
  have e2 : (((B - x.val : ℕ)) : ZMod B) = -x := by
    rw [Nat.cast_sub (le_of_lt hrB), ZMod.natCast_self, e1, zero_sub]
  have hsum : x.val + (B - x.val) = B := Nat.add_sub_cancel' (le_of_lt hrB)
  obtain ⟨c, hc⟩ := hB
  rcases le_total x.val (B - x.val) with hle | hle
  · refine ⟨x.val, hr0, by omega, Or.inl e1, Or.inl rfl⟩
  · refine ⟨B - x.val, by omega, by omega, Or.inr e2, Or.inr rfl⟩

/-- From ordered small reps with class correspondence, build a preimage. -/
private theorem exists_preimage_of_ordered {B : ℕ} (hB : Odd B) (hB3 : 3 < B)
    {q p : ℕ} {A D : Finset (ZMod B)} {xa xb : ZMod B}
    (hq1 : 1 ≤ q) (hqp : q < p) (hpm : p ≤ (B - 1) / 2)
    (hqa : ((q : ℕ) : ZMod B) = xa ∨ ((q : ℕ) : ZMod B) = -xa)
    (hpa : ((p : ℕ) : ZMod B) = xb ∨ ((p : ℕ) : ZMod B) = -xb)
    (hA : A = {xa, -xa}) (hD : D = {xb, -xb}) :
    ∃ d : ↥(TBset B), phiFun B d = {A, D} := by
  obtain ⟨c, hc⟩ := hB
  have hmB : 2 * ((B - 1) / 2) + 1 = B := by omega
  have hpB : p < B := by omega
  by_cases hodd : Odd (p + q)
  · have hsumB : p + q < B := by omega
    obtain ⟨k, hk⟩ := hodd
    have hodd : Odd (p + q) := ⟨k, hk⟩
    have hqk : q ≤ k := by omega
    have hW : p - q = 2 * (k - q) + 1 := by omega
    have hOdd2 : Odd (p - q) := ⟨k - q, hW⟩
    refine ⟨⟨(p + q, p - q), ?_⟩, ?_⟩
    · simp only [TBset, XBset, Set.mem_ofPred_eq]
      refine ⟨⟨by omega, by omega, by omega⟩, by omega, by omega, hodd, hOdd2⟩
    · have eU : ((p + q) + (p - q)) / 2 = p := by omega
      have eV : ((p + q) - (p - q)) / 2 = q := by omega
      have hV : (({(↑q : ZMod B), -(↑q : ZMod B)} : Finset (ZMod B))) = A := by
        rcases hqa with hqa | hqa
        · rw [hqa]; exact hA.symm
        · rw [hqa, neg_neg, Finset.pair_comm]; exact hA.symm
      have hU : (({(↑p : ZMod B), -(↑p : ZMod B)} : Finset (ZMod B))) = D := by
        rcases hpa with hpa | hpa
        · rw [hpa]; exact hD.symm
        · rw [hpa, neg_neg, Finset.pair_comm]; exact hD.symm
      simp only [phiFun]
      rw [eU, eV, hU, hV, Finset.pair_comm]
  · have hE : Even (p + q) := by
      rcases Nat.even_or_odd (p + q) with hE | hO
      · exact hE
      · exact absurd hO hodd
    have hcast : (((B - p : ℕ)) : ZMod B) = -↑p := by
      rw [Nat.cast_sub (le_of_lt hpB), ZMod.natCast_self, zero_sub]
    have hsumB : (B - p) + q < B := by omega
    obtain ⟨r, hr⟩ := hE
    have hrc : r ≤ c := by omega
    have hW : (B - p) + q = 2 * ((c - r) + q) + 1 := by omega
    have hW2 : (B - p) - q = 2 * (c - r) + 1 := by omega
    have hOdd : Odd ((B - p) + q) := ⟨(c - r) + q, hW⟩
    have hOdd2 : Odd ((B - p) - q) := ⟨c - r, hW2⟩
    refine ⟨⟨((B - p) + q, (B - p) - q), ?_⟩, ?_⟩
    · simp only [TBset, XBset, Set.mem_ofPred_eq]
      refine ⟨⟨by omega, by omega, by omega⟩, by omega, by omega, hOdd, hOdd2⟩
    · have eU : (((B - p) + q) + ((B - p) - q)) / 2 = B - p := by omega
      have eV : (((B - p) + q) - ((B - p) - q)) / 2 = q := by omega
      have hV : (({(↑q : ZMod B), -(↑q : ZMod B)} : Finset (ZMod B))) = A := by
        rcases hqa with hqa | hqa
        · rw [hqa]; exact hA.symm
        · rw [hqa, neg_neg, Finset.pair_comm]; exact hA.symm
      have hU : (({(↑(B - p) : ZMod B), -(↑(B - p) : ZMod B)} :
          Finset (ZMod B))) = D := by
        rw [hcast, neg_neg]
        rcases hpa with hpa | hpa
        · rw [hpa, Finset.pair_comm]; exact hD.symm
        · rw [hpa, neg_neg]; exact hD.symm
      simp only [phiFun]
      rw [eU, eV, hU, hV, Finset.pair_comm]

/-- Phi is surjective onto Proj. -/
private theorem phi_surj {B : ℕ} (hB : Odd B) (hB3 : 3 < B) {S : Finset (Finset (ZMod B))}
    (hS : S ∈ ProjSet B) : ∃ d : ↥(TBset B), phiFun B d = S := by
  have : NeZero B := ⟨by obtain ⟨c, hc⟩ := hB; omega⟩
  simp only [ProjSet, Set.mem_ofPred_eq] at hS
  obtain ⟨hcard, hmem⟩ := hS
  rw [Finset.card_eq_two] at hcard
  obtain ⟨C1, C2, h12, rfl⟩ := hcard
  obtain ⟨x1, hx10, hx1⟩ := hmem C1 (by simp)
  obtain ⟨x2, hx20, hx2⟩ := hmem C2 (by simp)
  obtain ⟨q1, hq11, hq1m, hq1c, -⟩ := class_small_rep hB hx10
  obtain ⟨q2, hq21, hq2m, hq2c, -⟩ := class_small_rep hB hx20
  have mk : ∀ (x : ZMod B) (C : Finset (ZMod B)) (hC : C = {x, -x})
      (h : ((q1 : ℕ) : ZMod B) = x ∨ ((q1 : ℕ) : ZMod B) = -x),
      C = ({((q1 : ℕ) : ZMod B), -((q1 : ℕ) : ZMod B)} : Finset (ZMod B)) := by
    intro x C hC h
    rw [hC]
    rcases h with h | h
    · rw [←h]
    · have h' : x = -((q1 : ℕ) : ZMod B) := by rw [h, neg_neg]
      rw [h', neg_neg, Finset.pair_comm]
  have hne : q1 ≠ q2 := by
    intro heq
    apply h12
    have e1 := mk x1 C1 hx1 hq1c
    have e2 := mk x2 C2 hx2 (by rw [heq]; exact hq2c)
    exact e1.trans e2.symm
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨d, hd⟩ := exists_preimage_of_ordered hB hB3 hq11 hlt hq2m hq1c hq2c hx1 hx2
    exact ⟨d, hd⟩
  · obtain ⟨d, hd⟩ := exists_preimage_of_ordered hB hB3 hq21 hgt hq1m hq2c hq1c hx2 hx1
    exact ⟨d, by rw [hd, Finset.pair_comm]⟩

/-- phiFun on an explicit pair (rfl). -/
private theorem phiFun_pair_eq {B : ℕ} {a b : ℕ} (hmem : (a, b) ∈ TBset B) :
    phiFun B (⟨(a, b), hmem⟩ : ↥(TBset B)) =
    ({{(((a + b) / 2 : ℕ) : ZMod B), -(((a + b) / 2 : ℕ) : ZMod B)},
      ({(((a - b) / 2 : ℕ) : ZMod B), -(((a - b) / 2 : ℕ) : ZMod B)} :
        Finset (ZMod B))} : Finset (Finset (ZMod B))) := rfl

/-- dblFun on an explicit pair of classes. -/
private theorem dblFun_pair {B : ℕ} {x y : ZMod B} :
    dblFun B ({{x, -x}, ({y, -y} : Finset (ZMod B))} : Finset (Finset (ZMod B))) =
    ({{x * 2, -(x * 2)}, ({y * 2, -(y * 2)} : Finset (ZMod B))} :
      Finset (Finset (ZMod B))) := by
  simp only [dblFun, Finset.image_insert, Finset.image_singleton, neg_mul]

/-- dblFun applied to Phi of a point. -/
private theorem dblFun_phiFun {B : ℕ} (p : ↥(TBset B)) :
    dblFun B (phiFun B p) =
    ({{(((p.1.1 + p.1.2) / 2 : ℕ) : ZMod B) * 2,
        -((((p.1.1 + p.1.2) / 2 : ℕ) : ZMod B) * 2)},
      ({(((p.1.1 - p.1.2) / 2 : ℕ) : ZMod B) * 2,
        -((((p.1.1 - p.1.2) / 2 : ℕ) : ZMod B) * 2)} : Finset (ZMod B))} :
      Finset (Finset (ZMod B))) := by
  have hP : phiFun B p =
      ({{(((p.1.1 + p.1.2) / 2 : ℕ) : ZMod B),
          -(((p.1.1 + p.1.2) / 2 : ℕ) : ZMod B)},
        ({(((p.1.1 - p.1.2) / 2 : ℕ) : ZMod B),
          -(((p.1.1 - p.1.2) / 2 : ℕ) : ZMod B)} : Finset (ZMod B))} :
        Finset (Finset (ZMod B))) := rfl
  rw [hP, dblFun_pair]

/-- S ≠ T from distinctness facts (for Step 7). -/
private theorem ST_ne_of {B d1 d2 : ℕ} (hne12 : d1 ≠ d2) (hnesum : d1 + d2 ≠ B) :
    (if 2 * d1 ≥ B then 2 * d1 - B else B - 2 * d1) ≠
      (if 2 * d2 ≥ B then 2 * d2 - B else B - 2 * d2) := by
  intro heq
  by_cases hA : 2 * d1 ≥ B <;> by_cases hC : 2 * d2 ≥ B
  · simp only [hA, hC, ite_true] at heq; omega
  · simp only [hA, hC, ite_true, ite_false] at heq; omega
  · simp only [hA, hC, ite_false, ite_true] at heq; omega
  · simp only [hA, hC, ite_false] at heq; omega

/-- Step 7 (conjunct 6): Phi conjugates kaprekar to doubling. -/
private theorem phi_conj {B : ℕ} (hB : Odd B) (_hB3 : 3 < B) (p : ↥(TBset B))
    (hmem : kapFun B p.1 ∈ TBset B) :
    phiFun B ⟨kapFun B p.1, hmem⟩ = dblFun B (phiFun B p) := by
  have hprop : p.1 ∈ TBset B := p.property
  simp only [TBset, XBset, Set.mem_ofPred_eq] at hprop
  obtain ⟨⟨h1, hB1, h2⟩, hlt, hpos, hodd1, hodd2⟩ := hprop
  have h2le : p.1.2 ≤ p.1.1 := le_of_lt hlt
  have hne12 : p.1.1 ≠ p.1.2 := ne_of_gt hlt
  have hEven : Even (p.1.1 + p.1.2) := Odd.add_odd hodd1 hodd2
  have hnesum : p.1.1 + p.1.2 ≠ B := by
    intro hcon
    rw [hcon] at hEven
    obtain ⟨r, hr⟩ := hEven
    obtain ⟨c, hc⟩ := hB
    omega
  have hST : (if 2 * p.1.1 ≥ B then 2 * p.1.1 - B else B - 2 * p.1.1) ≠
      (if 2 * p.1.2 ≥ B then 2 * p.1.2 - B else B - 2 * p.1.2) :=
    ST_ne_of hne12 hnesum
  have hKd := kapFun_ne_of_ne (d1 := p.1.1) (d2 := p.1.2) hB
    rfl rfl h1 hB1 h2 hpos hST
  rw [show (p.1.1, p.1.2) = p.1 from Prod.mk.eta] at hKd
  obtain ⟨h2u, h2v, huv, hd2, hv0, hvu, hsum, hodd⟩ := uv_facts p
  rw [dblFun_phiFun p]
  set u : ℕ := (p.1.1 + p.1.2) / 2 with hu
  set v : ℕ := (p.1.1 - p.1.2) / 2 with hv
  have hCv : ((((p.1.1 - p.1.2 : ℕ))) : ZMod B) = 2 * (↑v : ZMod B) := by
    rw [←h2v, Nat.cast_mul, Nat.cast_ofNat]
  have hmu : (↑u * 2 : ZMod B) = 2 * (↑u : ZMod B) := mul_comm _ _
  have hmv : (↑v * 2 : ZMod B) = 2 * (↑v : ZMod B) := mul_comm _ _
  have hCuC : (({-(2 * (↑u : ZMod B)), -(-(2 * (↑u : ZMod B)))} :
      Finset (ZMod B))) = {2 * (↑u : ZMod B), -(2 * (↑u : ZMod B))} := by
    rw [neg_neg, Finset.pair_comm]
  by_cases hA : 2 * p.1.1 ≥ B <;> by_cases hC : 2 * p.1.2 ≥ B
  · have eS : (if 2 * p.1.1 ≥ B then 2 * p.1.1 - B else B - 2 * p.1.1)
        = 2 * p.1.1 - B := ite_eq_left hA
    have eT : (if 2 * p.1.2 ≥ B then 2 * p.1.2 - B else B - 2 * p.1.2)
        = 2 * p.1.2 - B := ite_eq_left hC
    have hSTS : 2 * p.1.2 - B ≤ 2 * p.1.1 - B := by omega
    have hKd12 : kapFun B p.1 = (2 * p.1.1 - B, 2 * p.1.2 - B) := by
      rw [hKd, eS, eT, max_eq_left hSTS, min_eq_right hSTS]
    have hmem12 : (2 * p.1.1 - B, 2 * p.1.2 - B) ∈ TBset B := by
      rw [←hKd12]; exact hmem
    have hQ : (⟨kapFun B p.1, hmem⟩ : ↥(TBset B))
        = ⟨(2 * p.1.1 - B, 2 * p.1.2 - B), hmem12⟩ := Subtype.ext hKd12
    rw [hQ, phiFun_pair_eq hmem12]
    have eUK : ((2 * p.1.1 - B) + (2 * p.1.2 - B)) / 2 = p.1.1 + p.1.2 - B := by
      omega
    have eVK : ((2 * p.1.1 - B) - (2 * p.1.2 - B)) / 2 = p.1.1 - p.1.2 := by
      omega
    rw [eUK, eVK]
    have hge : p.1.1 + p.1.2 ≥ B := by omega
    have hCu : ((((p.1.1 + p.1.2 - B : ℕ))) : ZMod B) = 2 * (↑u : ZMod B) := by
      rw [Nat.cast_sub hge, ZMod.natCast_self, sub_zero, ←h2u, Nat.cast_mul,
        Nat.cast_ofNat]
    rw [hCu, hCv, hmu, hmv]
  · have eS : (if 2 * p.1.1 ≥ B then 2 * p.1.1 - B else B - 2 * p.1.1)
        = 2 * p.1.1 - B := ite_eq_left hA
    have eT : (if 2 * p.1.2 ≥ B then 2 * p.1.2 - B else B - 2 * p.1.2)
        = B - 2 * p.1.2 := ite_eq_right hC
    have h2lt : 2 * p.1.2 < B := lt_of_not_ge hC
    by_cases hAB : p.1.1 + p.1.2 ≥ B
    · have hSTle : B - 2 * p.1.2 ≤ 2 * p.1.1 - B := by omega
      have hKd12 : kapFun B p.1 = (2 * p.1.1 - B, B - 2 * p.1.2) := by
        rw [hKd, eS, eT, max_eq_left hSTle, min_eq_right hSTle]
      have hmem12 : (2 * p.1.1 - B, B - 2 * p.1.2) ∈ TBset B := by
        rw [←hKd12]; exact hmem
      have hQ : (⟨kapFun B p.1, hmem⟩ : ↥(TBset B))
          = ⟨(2 * p.1.1 - B, B - 2 * p.1.2), hmem12⟩ := Subtype.ext hKd12
      rw [hQ, phiFun_pair_eq hmem12]
      have eUK : ((2 * p.1.1 - B) + (B - 2 * p.1.2)) / 2 = p.1.1 - p.1.2 := by
        omega
      have eVK : ((2 * p.1.1 - B) - (B - 2 * p.1.2)) / 2 = p.1.1 + p.1.2 - B := by
        omega
      rw [eUK, eVK]
      have hCu : ((((p.1.1 + p.1.2 - B : ℕ))) : ZMod B) = 2 * (↑u : ZMod B) := by
        rw [Nat.cast_sub hAB, ZMod.natCast_self, sub_zero, ←h2u, Nat.cast_mul,
          Nat.cast_ofNat]
      rw [hCu, hCv, hmu, hmv]
      exact Finset.pair_comm _ _
    · have hAB' : p.1.1 + p.1.2 < B := lt_of_not_ge hAB
      have hSTle : 2 * p.1.1 - B ≤ B - 2 * p.1.2 := by omega
      have hKd12 : kapFun B p.1 = (B - 2 * p.1.2, 2 * p.1.1 - B) := by
        rw [hKd, eS, eT, max_eq_right hSTle, min_eq_left hSTle]
      have hmem12 : (B - 2 * p.1.2, 2 * p.1.1 - B) ∈ TBset B := by
        rw [←hKd12]; exact hmem
      have hQ : (⟨kapFun B p.1, hmem⟩ : ↥(TBset B))
          = ⟨(B - 2 * p.1.2, 2 * p.1.1 - B), hmem12⟩ := Subtype.ext hKd12
      rw [hQ, phiFun_pair_eq hmem12]
      have eUK : ((B - 2 * p.1.2) + (2 * p.1.1 - B)) / 2 = p.1.1 - p.1.2 := by
        omega
      have eVK : ((B - 2 * p.1.2) - (2 * p.1.1 - B)) / 2
          = B - (p.1.1 + p.1.2) := by omega
      rw [eUK, eVK]
      have hle : p.1.1 + p.1.2 ≤ B := le_of_lt hAB'
      have hCu' : ((((B - (p.1.1 + p.1.2) : ℕ))) : ZMod B) = -(2 * (↑u : ZMod B)) := by
        rw [Nat.cast_sub hle, ZMod.natCast_self, zero_sub, ←h2u, Nat.cast_mul,
          Nat.cast_ofNat]
      rw [hCu', hCv, hmu, hmv, hCuC]
      exact Finset.pair_comm _ _
  · exfalso; omega
  · have eS : (if 2 * p.1.1 ≥ B then 2 * p.1.1 - B else B - 2 * p.1.1)
        = B - 2 * p.1.1 := ite_eq_right hA
    have eT : (if 2 * p.1.2 ≥ B then 2 * p.1.2 - B else B - 2 * p.1.2)
        = B - 2 * p.1.2 := ite_eq_right hC
    have hSTle : B - 2 * p.1.1 ≤ B - 2 * p.1.2 := by omega
    have hKd12 : kapFun B p.1 = (B - 2 * p.1.2, B - 2 * p.1.1) := by
      rw [hKd, eS, eT, max_eq_right hSTle, min_eq_left hSTle]
    have hmem12 : (B - 2 * p.1.2, B - 2 * p.1.1) ∈ TBset B := by
      rw [←hKd12]; exact hmem
    have hQ : (⟨kapFun B p.1, hmem⟩ : ↥(TBset B))
        = ⟨(B - 2 * p.1.2, B - 2 * p.1.1), hmem12⟩ := Subtype.ext hKd12
    rw [hQ, phiFun_pair_eq hmem12]
    have eUK : ((B - 2 * p.1.2) + (B - 2 * p.1.1)) / 2
        = B - (p.1.1 + p.1.2) := by omega
    have eVK : ((B - 2 * p.1.2) - (B - 2 * p.1.1)) / 2 = p.1.1 - p.1.2 := by
      omega
    rw [eUK, eVK]
    have hle : p.1.1 + p.1.2 ≤ B := by omega
    have hCu' : ((((B - (p.1.1 + p.1.2) : ℕ))) : ZMod B) = -(2 * (↑u : ZMod B)) := by
      rw [Nat.cast_sub hle, ZMod.natCast_self, zero_sub, ←h2u, Nat.cast_mul,
        Nat.cast_ofNat]
    rw [hCu', hCv, hmu, hmv, hCuC]

/-- The bundled Phi map is bijective. -/
private theorem phi_bij {B : ℕ} (hB : Odd B) (hB3 : 3 < B) :
    Function.Bijective
      (fun d : ↥(TBset B) => (⟨phiFun B d, phi_mem_Proj d⟩ : ↥(ProjSet B))) := by
  constructor
  · intro a b hab
    have h : phiFun B a = phiFun B b := Subtype.ext_iff.mp hab
    exact phi_inj hB h
  · intro S
    obtain ⟨d, hd⟩ := phi_surj hB hB3 S.property
    exact ⟨d, Subtype.ext hd⟩

/-- The equivalence acts as Phi on points. -/
private theorem equiv_prop1 {B : ℕ} (hB : Odd B) (hB3 : 3 < B) (d : ↥(TBset B)) :
    (((Equiv.ofBijective _ (phi_bij hB hB3)) d : ↥(ProjSet B)).val :
      Finset (Finset (ZMod B))) = phiFun B d := rfl

/-! # Four-digit Kaprekar dynamics in odd bases -/

/--
**Structure of four-digit Kaprekar dynamics in odd bases.** Let $B > 3$ be an odd integer.
For a pair of natural numbers $d = (d_1, d_2)$, let $K(d) = (a - e, b - c)$, where
$a \ge b \ge c \ge e$ are the four numbers $d_1 - 1, B - 1, B - 1, B - d_1$ if $d_2 = 0$, and
$d_1, d_2 - 1, B - d_2 - 1, B - d_1$ if $d_2 \ne 0$, sorted in decreasing order (subtraction is
truncated at $0$). Let $X_B$ be the set of pairs with $1 \le d_1 < B$ and $d_2 \le d_1$, and let
$T_B$ be the set of pairs in $X_B$ with $0 < d_2 < d_1$ and $d_1$, $d_2$ both odd. Let
$\mathcal{P}$ be the set of two-element sets $S$ of subsets of $\mathbb{Z}/B\mathbb{Z}$ such that
every $C \in S$ has the form $\{x, -x\}$ with $x \ne 0$. For a set $S$ of subsets of
$\mathbb{Z}/B\mathbb{Z}$ let $2S = \{2C : C \in S\}$, where $2C = \{2y : y \in C\}$, and for
$d \in T_B$ let $\Phi(d) = \{\{u, -u\}, \{v, -v\}\}$, where $u$ and $v$ are the residues of
$(d_1 + d_2)/2$ and $(d_1 - d_2)/2$ modulo $B$. Then $K$ maps $T_B$ into itself, the third
iterate $K^3$ maps $X_B$ into $T_B$, $S \mapsto 2S$ maps $\mathcal{P}$ into itself, $\Phi$ is a
bijection from $T_B$ onto $\mathcal{P}$, and $\Phi(K(d)) = 2\,\Phi(d)$ for every $d \in T_B$.

Here a pair $(d_1, d_2) \in X_B$ stands for the four-digit base-$B$ numbers whose digits, sorted
as $a \ge b \ge c \ge e$, satisfy $a - e = d_1$ and $b - c = d_2$; the four numbers listed above
are the base-$B$ digits of their Kaprekar image, so $K$ is the Kaprekar map on these pairs.

Proves `Wanted` entry `four_digit_kaprekar_structural_classification`.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, "Four-Digit Kaprekar Dynamics in Odd Bases", Journal of Integer Sequences 29 (2026), Article 26.4.7, Theorem `thm:structural`, lines 220-230, <https://cs.uwaterloo.ca/journals/JIS/VOL29/Ono/ono3.tex>.
-/
theorem four_digit_kaprekar_structural_classification
    (B : ℕ) (hB : Odd B) (hB3 : 3 < B) :
    let X_B : Set (ℕ × ℕ) :=
      {d | 1 ≤ d.1 ∧ d.1 < B ∧ d.2 ≤ d.1};
    let T_B : Set (ℕ × ℕ) :=
      {d | d ∈ X_B ∧ d.2 < d.1 ∧ 0 < d.2 ∧ Odd d.1 ∧ Odd d.2};
    let kaprekar : ℕ × ℕ → ℕ × ℕ := fun d =>
      match List.insertionSort (· ≥ ·)
        (if d.2 = 0 then [d.1 - 1, B - 1, B - 1, B - d.1]
          else [d.1, d.2 - 1, B - d.2 - 1, B - d.1]) with
      | [a, b, c, e] => (a - e, b - c)
      | _ => (0, 0);
    let Phi : ↥T_B → Finset (Finset (ZMod B)) := fun d =>
      let u : ZMod B := (((d.1.1 + d.1.2) / 2 : ℕ) : ZMod B);
      let v : ZMod B := (((d.1.1 - d.1.2) / 2 : ℕ) : ZMod B);
      {{u, -u}, {v, -v}};
    let dbl : Finset (Finset (ZMod B)) → Finset (Finset (ZMod B)) :=
      fun S => S.image (fun C => C.image (· * 2));
    let Proj : Set (Finset (Finset (ZMod B))) :=
      {S | S.card = 2 ∧ ∀ C ∈ S, ∃ x : ZMod B, x ≠ 0 ∧ C = {x, -x}};
    ∃ hstable : Set.MapsTo kaprekar T_B T_B,
      Set.MapsTo (kaprekar^[3]) X_B T_B ∧
        (∀ S ∈ Proj, dbl S ∈ Proj) ∧
        (∀ d : ↥T_B, Phi d ∈ Proj) ∧
        ∃ e : ↥T_B ≃ ↥Proj,
          (∀ d, (e d : Finset (Finset (ZMod B))) = Phi d) ∧
            ∀ d : ↥T_B,
              (e ⟨kaprekar d.1, hstable d.2⟩ : Finset (Finset (ZMod B))) =
                dbl (Phi d) := by
  intro X_B T_B kaprekar Phi dbl Proj
  have hbij := phi_bij hB hB3
  refine ⟨kap_maps_T B hB hB3, kap_iter3 B hB hB3, ?_, ?_,
    ⟨Equiv.ofBijective _ hbij, ?_, ?_⟩⟩
  · exact fun S hS => dbl_preserves hB hS
  · exact fun d => phi_mem_Proj d
  · intro d
    exact equiv_prop1 hB hB3 d
  · intro d
    have h1 := equiv_prop1 hB hB3
      (⟨kaprekar d.1, (kap_maps_T B hB hB3) d.2⟩ : ↥(TBset B))
    exact h1.trans (phi_conj hB hB3 _ _)

end MetaMathlibExt
end
