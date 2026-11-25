/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.CyclicPatternAvoidingStacks
import Mathlib.Data.List.Permutation

/-!
# Counting permutations sorted by the consecutive cyclic 321-stack

The consecutive cyclic 321-stack sorts exactly `2 ^ (n - 2)` permutations of length `n ≥ 2`.
We count the possible tails by successively choosing an endpoint of the remaining interval.
-/

namespace MetaMathlibExt
namespace card_sortedPermutations_consecutiveCyclicStackSort_321

private def bad (st : List ℕ) : Prop :=
  ∃ p ∈ [3, 2, 1].cyclicPermutations, ContainsConsecutivePatternSeq st p

private instance decidableBad : DecidablePred bad := fun st => by
  unfold bad
  infer_instance

private abbrev run := restrictedStackSortAux bad

private theorem rotations :
    ([3, 2, 1] : List ℕ).cyclicPermutations = [[3, 2, 1], [2, 1, 3], [1, 3, 2]] := by decide

private theorem bad_short (x : ℕ) (s : List ℕ) (hs : s.length ≤ 1) : ¬bad (x :: s) := by
  rcases s with _ | ⟨y, _ | ⟨z, t⟩⟩ <;>
    simp [bad, rotations, ContainsConsecutivePatternSeq, SameRelativeOrder, List.tails] at *

private theorem bad_three (x a b : ℕ) (st : List ℕ) :
    bad (x :: a :: b :: st) ↔
      (b < a ∧ a < x) ∨ (a < x ∧ x < b) ∨ (x < b ∧ b < a) ∨ bad (a :: b :: st) := by
  have peel (p : List ℕ) (hp : p.length = 3) :
      ContainsConsecutivePatternSeq (x :: a :: b :: st) p ↔
        SameRelativeOrder [x, a, b] p ∨ ContainsConsecutivePatternSeq (a :: b :: st) p := by
    simp [ContainsConsecutivePatternSeq, hp]
  simp only [bad, rotations, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    ↓existsAndEq, true_and]
  rw [peel [3, 2, 1] rfl, peel [2, 1, 3] rfl, peel [1, 3, 2] rfl]
  simp [SameRelativeOrder, Nat.forall_lt_succ_right]
  grind

private theorem increasing_good {st : List ℕ} (hs : st.Pairwise (· < ·)) : ¬bad st := by
  match st with
  | [] => decide
  | [x] => exact bad_short x [] (by decide)
  | [x, y] => exact bad_short x [y] (by simp)
  | x :: a :: b :: st =>
    have h₁ : x < a := List.pairwise_cons.mp hs |>.1 _ (by simp)
    have h₂ : a < b := List.pairwise_cons.mp hs.of_cons |>.1 _ (by simp)
    rw [bad_three]
    simp [h₁.not_gt, h₂.not_gt, increasing_good hs.of_cons]

private theorem bad_push_iff {x a b : ℕ} {st : List ℕ}
    (hs : (a :: b :: st).Pairwise (· < ·)) :
    bad (x :: a :: b :: st) ↔ a < x ∧ x < b := by
  have hab := (List.pairwise_cons.mp hs).1 b (by simp)
  rw [bad_three]
  simp [hab.not_gt, increasing_good hs]

private def popCount (x : ℕ) (st : List ℕ) : ℕ :=
  ((List.range (st.length + 1)).find? fun k => !decide (bad (x :: st.drop k))).getD st.length

private theorem popCount_cons (x y : ℕ) (st : List ℕ) :
    popCount x (y :: st) = if bad (x :: y :: st) then popCount x st + 1 else 0 := by
  unfold popCount
  rw [List.length_cons, List.range_succ_eq_map, List.find?_cons, List.find?_map]
  simp only [List.drop_zero, List.drop_succ_cons, Function.comp_def]
  split_ifs <;> simp_all

private theorem run_pop {x y xs st} (hb : bad (x :: y :: st)) :
    run (x :: xs) (y :: st) = y :: run (x :: xs) st := by
  change (y :: st).take (popCount x (y :: st)) ++
    run xs (x :: (y :: st).drop (popCount x (y :: st))) =
    y :: (st.take (popCount x st) ++ run xs (x :: st.drop (popCount x st)))
  simp [popCount_cons, hb]

private theorem run_push {x xs st} (hg : ¬bad (x :: st)) :
    run (x :: xs) st = run xs (x :: st) := by
  have hz : popCount x st = 0 := by
    cases st with
    | nil => simp [popCount, List.range_succ_eq_map, hg]
    | cons y st => simp [popCount_cons, hg]
  change st.take (popCount x st) ++ run xs (x :: st.drop (popCount x st)) = _
  simp [hz]

-- Entries already on the stack leave it in their current relative order.
private theorem stack_sublist (xs st : List ℕ) : st.Sublist (run xs st) := by
  induction xs generalizing st with
  | nil => exact .refl _
  | cons x xs ih =>
    let k := popCount x st
    change st.Sublist (st.take k ++ run xs (x :: st.drop k))
    have h := (List.sublist_cons_self x (st.drop k)).trans (ih (x :: st.drop k))
    simpa using (List.Sublist.refl (st.take k)).append h

private theorem increasing_cons {x a : ℕ} {st : List ℕ}
    (hx : x < a) (hs : (a :: st).Pairwise (· < ·)) : (x :: a :: st).Pairwise (· < ·) :=
  hs.cons (fun y hy => (List.mem_cons.mp hy).elim (fun h => h ▸ hx)
    (fun h => hx.trans ((List.pairwise_cons.mp hs).1 y h)))

private theorem push_smaller {x a : ℕ} {st xs : List ℕ}
    (hx : x < a) (hs : (a :: st).Pairwise (· < ·)) :
    run (x :: xs) (a :: st) = run xs (x :: a :: st) :=
  run_push (increasing_good (increasing_cons hx hs))

-- For an increasing output, all future input is smaller than the second stack entry.
-- A push either retains the second entry or makes the old top the new second entry.
private theorem below_second {xs : List ℕ} {a b : ℕ} {st : List ℕ}
    (hout : (run xs (a :: b :: st)).Pairwise (· < ·)) : ∀ y ∈ xs, y < b := by
  induction xs generalizing a b st with
  | nil => simp
  | cons x xs ih =>
    have hs := hout.sublist (stack_sublist _ _)
    have hab := (List.pairwise_cons.mp hs).1 b (by simp)
    by_cases hm : a < x ∧ x < b
    · rw [run_pop ((bad_push_iff hs).mpr hm), push_smaller hm.2 hs.of_cons] at hout
      exact List.forall_mem_cons.mpr ⟨hm.2, ih hout.of_cons⟩
    · rw [run_push (fun h => hm ((bad_push_iff hs).mp h))] at hout
      have hnew := hout.sublist (stack_sublist _ _)
      have hxa := (List.pairwise_cons.mp hnew).1 a (by simp)
      exact List.forall_mem_cons.mpr ⟨hxa.trans hab, fun y hy => (ih hout y hy).trans hab⟩

private def prepend (a : ℕ) : List ℕ ↪ List ℕ := ⟨List.cons a, List.cons_injective⟩

-- The interval has k + 1 entries. At a singleton the two endpoints coincide.
private def choices (lo : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[lo]}
  | k + 1 =>
    (choices (lo + 1) k).map (prepend lo) ∪ (choices lo k).map (prepend (lo + (k + 1)))

private theorem cons_mem_choices (lo k a : ℕ) (s : List ℕ) :
    a :: s ∈ choices lo (k + 1) ↔
      (a = lo ∧ s ∈ choices (lo + 1) k) ∨ (a = lo + (k + 1) ∧ s ∈ choices lo k) := by
  simp [choices, Finset.mem_map, prepend, eq_comm, and_comm]

private theorem card_choices (lo k : ℕ) : (choices lo k).card = 2 ^ k := by
  induction k generalizing lo with
  | zero => simp [choices]
  | succ k ih =>
    rw [choices, Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map, ih, ih,
      Nat.pow_succ]
    · omega
    · refine Finset.disjoint_left.mpr ?_
      rintro _ h₁ h₂
      obtain ⟨s, _, rfl⟩ := Finset.mem_map.mp h₁
      obtain ⟨t, _, he⟩ := Finset.mem_map.mp h₂
      have := (List.cons.inj he).1
      omega

private theorem range_perm_max (lo k : ℕ) :
    (List.range' lo (k + 1)).Perm ((lo + k) :: List.range' lo k) := by
  rw [List.range'_concat, Nat.one_mul]
  exact List.perm_append_singleton _ _

private theorem choices_perm {lo k : ℕ} {s : List ℕ} (hs : s ∈ choices lo k) :
    s.Perm (List.range' lo (k + 1)) := by
  induction k generalizing lo s with
  | zero =>
    simpa [choices] using hs
  | succ k ih =>
    rw [choices, Finset.mem_union] at hs
    rcases hs with h | h <;> obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp h
    · rw [List.range'_succ]
      exact (ih ht).cons lo
    · exact ((ih ht).cons _).trans (range_perm_max ..).symm

private theorem increasing_target {lo k b : ℕ} {st : List ℕ} (hb : lo + k ≤ b)
    (hs : (b :: st).Pairwise (· < ·)) : (List.range' lo k ++ b :: st).Pairwise (· < ·) := by
  refine List.pairwise_append.mpr ⟨List.pairwise_lt_range', hs, ?_⟩
  intro x hx y hy
  have hxb := (List.mem_range'_1.mp hx).2.trans_le hb
  rcases List.mem_cons.mp hy with rfl | hm
  · exact hxb
  · exact hxb.trans ((List.pairwise_cons.mp hs).1 _ hm)

-- With a larger entry beneath the input interval, peeling a minimum immediately emits it.
-- Peeling a maximum extends the increasing stack beneath the remaining interval.
private theorem sorts_iff_choices {k lo b : ℕ} {s st : List ℕ}
    (hp : s.Perm (List.range' lo (k + 1))) (hb : lo + k < b)
    (hs : (b :: st).Pairwise (· < ·)) :
    run s (b :: st) = List.range' lo (k + 1) ++ b :: st ↔ s ∈ choices lo k := by
  induction k generalizing lo b s st with
  | zero =>
    rw [List.range'_one] at hp ⊢
    obtain rfl := hp.eq_singleton
    rw [push_smaller (by omega : lo < b) hs]
    simp [run, restrictedStackSortAux, choices]
  | succ k ih =>
    have hlen := hp.length_eq
    simp only [List.length_range'] at hlen
    rcases s with _ | ⟨a, _ | ⟨x, xs⟩⟩
    · simp at hlen
    · simp at hlen
    have bounds {y} (hy : y ∈ a :: x :: xs) := List.mem_range'_1.mp (hp.mem_iff.mp hy)
    have ha := bounds (y := a) (by simp)
    have hx := bounds (y := x) (by simp)
    have hab : a < b := by omega
    have hxb : x < b := by omega
    have habs := increasing_cons hab hs
    rw [push_smaller hab hs, cons_mem_choices]
    have hne : a ≠ x := by
      have hn := hp.nodup_iff.mpr (List.nodup_range' 1)
      exact fun he => hn.notMem (by simp [he])
    by_cases hmin : a = lo
    · subst a
      rw [List.range'_succ] at hp ⊢
      have hpop := (bad_push_iff habs).mpr (show lo < x ∧ x < b by omega)
      rw [run_pop hpop, List.cons_append, List.cons_inj_right, ih hp.cons_inv (by omega) hs]
      simp
    · by_cases hmax : a = lo + (k + 1)
      · have hr := range_perm_max lo (k + 1)
        rw [← hmax] at hr
        have ht := (hp.trans hr).cons_inv
        rw [List.range'_concat, Nat.one_mul, ← hmax, List.append_assoc, List.singleton_append]
        have hlt : lo + k < a := by omega
        rw [ih ht hlt habs]
        simp [hmax]
      · simp only [hmin, hmax, false_and, or_self, iff_false]
        intro he
        rcases lt_or_gt_of_ne hne with hax | hxa
        · rw [run_pop ((bad_push_iff habs).mpr ⟨hax, hxb⟩), List.range'_succ,
            List.cons_append] at he
          exact hmin (List.cons.inj he).1
        · rw [push_smaller hxa habs] at he
          have hout := increasing_target (k := k + 1 + 1) (lo := lo) (by omega) hs
          rw [← he] at hout
          have hmem : lo + (k + 1) ∈ a :: x :: xs :=
            hp.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
          have htail : lo + (k + 1) ∈ xs := by
            simpa [List.mem_cons, Ne.symm hmax, show lo + (k + 1) ≠ x by omega] using hmem
          have := below_second hout _ htail
          omega

private theorem first_is_max {a x n : ℕ} {xs : List ℕ}
    (hp : (a :: x :: xs).Perm (List.range' 1 (n + 2)))
    (he : run (a :: x :: xs) [] = List.range' 1 (n + 2)) : a = n + 2 := by
  rw [run_push (bad_short a [] (by simp)), run_push (bad_short x [a] (by simp))] at he
  have hout : (run xs [x, a]).Pairwise (· < ·) := he ▸ List.pairwise_lt_range'
  have hxa := (List.pairwise_cons.mp (hout.sublist (stack_sublist xs [x, a]))).1 a (by simp)
  have hmem : n + 2 ∈ a :: x :: xs := hp.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
  have ha := List.mem_range'_1.mp (hp.mem_iff.mp (List.mem_cons_self (a := a)))
  rcases List.mem_cons.mp hmem with h | h
  · exact h.symm
  · rcases List.mem_cons.mp h with h | h
    · omega
    · have := below_second hout _ h
      omega

private theorem sorted_eq_choices (k : ℕ) :
    sortedPermutations (consecutiveCyclicStackSort [3, 2, 1]) (k + 2) =
      (choices 1 k).map (prepend (k + 2)) := by
  ext s
  simp only [sortedPermutations, Finset.mem_filter, List.mem_toFinset, List.mem_permutations,
    Finset.mem_map]
  change s.Perm (List.range' 1 (k + 2)) ∧ run s [] = List.range' 1 (k + 2) ↔ _
  have hr := range_perm_max 1 (k + 1)
  have hlast : 1 + (k + 1) = k + 2 := by omega
  rw [hlast] at hr
  have ends : List.range' 1 (k + 2) = List.range' 1 (k + 1) ++ [k + 2] := by
    rw [List.range'_concat, Nat.one_mul, hlast]
  have hsort {t : List ℕ} (ht : t.Perm (List.range' 1 (k + 1))) :
      run ((k + 2) :: t) [] = List.range' 1 (k + 2) ↔ t ∈ choices 1 k := by
    rw [run_push (bad_short _ [] (by simp)), ends]
    exact sorts_iff_choices ht (by omega) (by simp)
  constructor
  · rintro ⟨hp, he⟩
    have hlen := hp.length_eq
    simp only [List.length_range'] at hlen
    rcases s with _ | ⟨a, _ | ⟨x, xs⟩⟩
    · simp at hlen
    · simp at hlen
    obtain rfl := first_is_max hp he
    exact ⟨_, (hsort (hp.trans hr).cons_inv).mp he, rfl⟩
  · rintro ⟨t, h, rfl⟩
    have ht := choices_perm h
    exact ⟨((ht.cons _).trans hr.symm), (hsort ht).mpr h⟩

end card_sortedPermutations_consecutiveCyclicStackSort_321

open card_sortedPermutations_consecutiveCyclicStackSort_321 in
/-- **Permutations sorted by the consecutive $321$-cyclic stack.** Let $n \ge 2$, let
$s^{[321]}$ be the stack-sorting map whose stack, read from top to bottom, avoids every rotation
of $321$ as a consecutive pattern, and let $\mathrm{Sort}_n(s^{[321]})$ be the set of permutations
of $[n] = \{1, \dots, n\}$ that $s^{[321]}$ maps to the identity $12 \cdots n$. Then
$|\mathrm{Sort}_n(s^{[321]})| = 2^{n-2}$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Theorem 4 (`integers-2026-A15-thm-4`). -/
public theorem card_sortedPermutations_consecutiveCyclicStackSort_321 {n : ℕ}
    (hn : 2 ≤ n) :
    (sortedPermutations (consecutiveCyclicStackSort [3, 2, 1]) n).card = 2 ^ (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp [sorted_eq_choices, card_choices]

end MetaMathlibExt
