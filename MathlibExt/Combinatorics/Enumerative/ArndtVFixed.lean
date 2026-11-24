/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ArndtV
public import Mathlib.Data.Nat.Fib.Basic

/-!
# Compositions fixed by the map V

`arndtV_fixed_iff_and_count` characterizes the fixed compositions by their parts and
counts them in terms of the Fibonacci sequence.
-/

namespace MetaMathlibExt
namespace arndtV_fixed_iff_and_count

-- The image of a pair has the same weight as the pair. If it starts a fixed list,
-- its run of ones must have length one, since its terminating part is greater than one.
private theorem run_eq_pair {r t a b : ℕ} {ys xs : List ℕ}
    (hb : 0 < b) (ht : 1 < t) (hs : r + t = a + b) :
    List.replicate r 1 ++ t :: ys = a :: b :: xs ↔
      a = 1 ∧ r = 1 ∧ t = b ∧ ys = xs := by
  cases r with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, List.cons.injEq]
    omega
  | succ r =>
    cases r with
    | zero => simp [eq_comm]
    | succ r =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq]
      omega

private theorem fixed_pair {a b : ℕ} {xs : List ℕ} (ha : 0 < a) (hb : 0 < b) :
    arndtV (a :: b :: xs) = a :: b :: xs ↔
      a = 1 ∧ Odd b ∧ 3 ≤ b ∧ arndtV xs = xs := by
  rw [arndtV]
  split <;> rename_i hab <;> simp only [List.append_assoc, List.singleton_append]
  · rw [run_eq_pair hb (by omega) (by omega)]
    omega
  · rw [run_eq_pair hb (by omega) (by omega), Nat.odd_iff]
    constructor
    · rintro ⟨rfl, hr, he, hxs⟩
      exact ⟨rfl, by omega, by omega, hxs⟩
    · rintro ⟨rfl, ho, hb, hxs⟩
      exact ⟨rfl, by omega, by omega, hxs⟩

private theorem fixed_single (a : ℕ) : arndtV [a] = [a] ↔ a = 1 := by
  constructor
  · intro h
    simpa [arndtV] using congrArg List.length h
  · rintro rfl
    rfl

private def Pattern (xs : List ℕ) : Prop :=
  ∀ (i : ℕ) (h : i < xs.length),
    if i % 2 = 0 then xs[i] = 1 else Odd xs[i] ∧ 3 ≤ xs[i]

private theorem pattern_pair (a b : ℕ) (xs : List ℕ) :
    Pattern (a :: b :: xs) ↔ a = 1 ∧ Odd b ∧ 3 ≤ b ∧ Pattern xs := by
  constructor
  · intro h
    have ha := h 0 (by simp)
    have hb := h 1 (by simp)
    change a = 1 at ha
    change Odd b ∧ 3 ≤ b at hb
    refine ⟨ha, hb.1, hb.2, fun i hi => ?_⟩
    have hp : i.succ.succ % 2 = i % 2 := by omega
    have htail := h i.succ.succ (by simpa using hi)
    have he : (a :: b :: xs)[i.succ.succ]'(by simpa using hi) = xs[i] := rfl
    simpa only [he, hp] using htail
  · rintro ⟨ha, ho, hb, ht⟩ (_ | _ | i) hi
    · simpa using ha
    · simpa using And.intro ho hb
    · have hp : i.succ.succ % 2 = i % 2 := by omega
      simpa only [List.getElem_cons_succ, hp] using ht i (by simpa using hi)

private theorem fixed_iff_pattern (xs : List ℕ) (hpos : ∀ a ∈ xs, 0 < a) :
    arndtV xs = xs ↔ Pattern xs := by
  induction xs using arndtV.induct with
  | case1 => simp [arndtV, Pattern]
  | case2 a => simp [fixed_single, Pattern]
  | case3 a b xs ih =>
    rw [fixed_pair (hpos a (by simp)) (hpos b (by simp)), pattern_pair,
      ih (fun x hx => hpos x (by simp [hx]))]

private def fixedComps (n : ℕ) : Finset (Composition n) :=
  Finset.univ.filter fun c => arndtV c.blocks = c.blocks

private def fixedLists (n : ℕ) : Finset (List ℕ) :=
  (fixedComps n).map ⟨Composition.blocks, fun _ _ => Composition.ext⟩

private theorem mem_fixedLists {xs : List ℕ} {n : ℕ} :
    xs ∈ fixedLists n ↔ xs.sum = n ∧ Pattern xs := by
  simp only [fixedLists, Finset.mem_map, fixedComps, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.blocks_sum, (fixed_iff_pattern _ fun _ => c.blocks_pos).mp hc⟩
  · rintro ⟨hs, hp⟩
    have hpos : ∀ a ∈ xs, 0 < a := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      have := hp i hi
      split at this <;> omega
    exact ⟨⟨xs, fun h => hpos _ h, hs⟩, (fixed_iff_pattern xs hpos).mpr hp, rfl⟩

private theorem exists_pair_of_mem {xs : List ℕ} {n : ℕ} (hn : 2 ≤ n)
    (hx : xs ∈ fixedLists n) : ∃ b ys, xs = 1 :: b :: ys ∧ 3 ≤ b := by
  obtain ⟨hs, hp⟩ := mem_fixedLists.mp hx
  match xs with
  | [] => simp at hs; omega
  | [a] => simp [Pattern] at hp; simp at hs; omega
  | a :: b :: ys =>
    obtain ⟨rfl, _, hb, _⟩ := (pattern_pair ..).mp hp
    exact ⟨b, ys, rfl, hb⟩

private def increaseSecond : List ℕ ↪ List ℕ where
  toFun xs := xs.modify 1 (· + 2)
  inj' := by
    apply Function.LeftInverse.injective (g := fun xs : List ℕ => xs.modify 1 (· - 2))
    intro xs
    simp only [List.modify_modify_eq, Function.comp_def, Nat.add_sub_cancel]
    exact List.modify_id 1 xs

private def prependPair : List ℕ ↪ List ℕ where
  toFun xs := 1 :: 3 :: xs
  inj' := by intro x y; simp

-- The images are distinguished by the second part: three for a new pair, at least five
-- for a pair whose second part was increased.
private theorem count_recurrence (n : ℕ) :
    (fixedLists (n + 5)).card = (fixedLists (n + 3)).card + (fixedLists (n + 1)).card := by
  let longer := (fixedLists (n + 3)).map increaseSecond
  let prefixed := (fixedLists (n + 1)).map prependPair
  have hd : Disjoint longer prefixed := by
    apply Finset.disjoint_left.mpr
    intro xs hl hp
    obtain ⟨l, hmem, rfl⟩ := Finset.mem_map.mp hl
    obtain ⟨b, ys, rfl, hb⟩ := exists_pair_of_mem (n := n + 3) (by omega) hmem
    obtain ⟨z, _, hz⟩ := Finset.mem_map.mp hp
    change 1 :: 3 :: z = 1 :: (b + 2) :: ys at hz
    simp only [List.cons.injEq] at hz
    omega
  have hu : fixedLists (n + 5) = longer ∪ prefixed := by
    ext xs
    constructor
    · intro hx
      obtain ⟨b, ys, rfl, hb⟩ := exists_pair_of_mem (by omega) hx
      obtain ⟨hs, ho, -, hy⟩ : (1 + (b + ys.sum) = n + 5) ∧ Odd b ∧ 3 ≤ b ∧ Pattern ys := by
        simpa [mem_fixedLists, pattern_pair] using hx
      by_cases h : b = 3
      · subst b
        exact Finset.mem_union_right _ (Finset.mem_map.mpr
          ⟨ys, mem_fixedLists.mpr ⟨by omega, hy⟩, rfl⟩)
      · have hodd := Nat.odd_iff.mp ho
        apply Finset.mem_union_left _ (Finset.mem_map.mpr ⟨1 :: (b - 2) :: ys, ?_, ?_⟩)
        · simp [mem_fixedLists, pattern_pair, Nat.odd_iff, hy]
          omega
        · change 1 :: (b - 2 + 2) :: ys = _
          rw [Nat.sub_add_cancel (by omega)]
    · intro hx
      rcases Finset.mem_union.mp hx with hl | hp
      · obtain ⟨l, hmem, rfl⟩ := Finset.mem_map.mp hl
        obtain ⟨b, ys, rfl, hb⟩ := exists_pair_of_mem (n := n + 3) (by omega) hmem
        change 1 :: (b + 2) :: ys ∈ fixedLists (n + 5)
        simp only [mem_fixedLists, List.sum_cons, pattern_pair, true_and, Nat.odd_iff] at hmem ⊢
        exact ⟨by omega, by omega, by omega, hmem.2.2.2⟩
      · obtain ⟨ys, hy, rfl⟩ := Finset.mem_map.mp hp
        change 1 :: 3 :: ys ∈ fixedLists (n + 5)
        obtain ⟨hs, hy⟩ := mem_fixedLists.mp hy
        simp [mem_fixedLists, pattern_pair, Nat.odd_iff, hy, hs]
        omega
  rw [hu, Finset.card_union_of_disjoint hd]
  simp [longer, prefixed]

private theorem small_lists (n : ℕ) (hn : n ≤ 4) :
    fixedLists n = ({[], [1], [1, 3]} : Finset (List ℕ)).filter (·.sum = n) := by
  ext xs
  rw [mem_fixedLists, Finset.mem_filter]
  constructor
  · rintro ⟨hs, hp⟩
    refine ⟨?_, hs⟩
    match xs with
    | [] => simp
    | [a] => simpa [Pattern] using hp
    | a :: b :: ys =>
      obtain ⟨rfl, _, hb, ht⟩ := (pattern_pair ..).mp hp
      simp only [List.sum_cons] at hs
      have hb3 : b = 3 := by omega
      have hempty : ys = [] := by
        cases ys with
        | nil => rfl
        | cons d ds =>
          have hd := ht 0 (by simp)
          simp at hd hs
          omega
      simp [hb3, hempty]
  · rintro ⟨h, hs⟩
    refine ⟨hs, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl
    · simp [Pattern]
    · simp [Pattern]
    · rw [pattern_pair]
      simp [Pattern, Nat.odd_iff]

private theorem small_counts :
    (fixedLists 1).card = 1 ∧ (fixedLists 4).card = 1 ∧
      (fixedLists 2).card = 0 ∧ (fixedLists 3).card = 0 := by
  simp only [small_lists _ (by decide : 1 ≤ 4), small_lists _ (by decide : 4 ≤ 4),
    small_lists _ (by decide : 2 ≤ 4), small_lists _ (by decide : 3 ≤ 4)]
  decide

private theorem fib_counts (k : ℕ) :
    (fixedLists (2 * k + 2)).card = Nat.fib k ∧ (fixedLists (2 * k + 3)).card = Nat.fib k := by
  obtain ⟨h1, h4, h2, h3⟩ := small_counts
  induction k using Nat.twoStepInduction with
  | zero => exact ⟨h2, h3⟩
  | one =>
    have h5 : (fixedLists 5).card = (fixedLists 3).card + (fixedLists 1).card := count_recurrence 0
    exact ⟨h4, by simpa [h1, h3] using h5⟩
  | more k ih₀ ih₁ =>
    have he := count_recurrence (2 * k + 1)
    have ho := count_recurrence (2 * k + 2)
    rw [Nat.fib_add_two]
    simp only [Nat.mul_succ, Nat.add_assoc, Nat.reduceAdd] at he ho ih₁ ⊢
    omega

end arndtV_fixed_iff_and_count

open arndtV_fixed_iff_and_count

/-- **Compositions fixed by $V$ and their Fibonacci count.** A composition $(c_1, \dots, c_m)$
of $n$ is fixed by the map $V$ if and only if $c_i = 1$ for every odd $i$ and $c_i$ is odd and
at least $3$ for every even $i$. Let $c_V(n)$ be the number of compositions of $n$ fixed by $V$.
Then $c_V(n) = c_V(n - 2) + c_V(n - 4)$ for every $n \ge 5$, $c_V(1) = c_V(4) = 1$,
$c_V(2) = c_V(3) = 0$, and $c_V(2j) = c_V(2j + 1) = F_{j-1}$ for every $j \ge 1$, where $F$ is
the Fibonacci sequence with $F_0 = 0$ and $F_1 = 1$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Proposition 2 (`integers-2026-A64-prop-2`). -/
public theorem arndtV_fixed_iff_and_count :
    (∀ (n : ℕ) (c : Composition n), arndtV c.blocks = c.blocks ↔
      ∀ (i : ℕ) (h : i < c.blocks.length),
        if i % 2 = 0 then c.blocks[i] = 1 else Odd c.blocks[i] ∧ 3 ≤ c.blocks[i]) ∧
    (∀ n : ℕ, 5 ≤ n →
      (Finset.univ.filter fun c : Composition n => arndtV c.blocks = c.blocks).card =
        (Finset.univ.filter fun c : Composition (n - 2) => arndtV c.blocks = c.blocks).card +
          (Finset.univ.filter fun c : Composition (n - 4) => arndtV c.blocks = c.blocks).card) ∧
    (Finset.univ.filter fun c : Composition 1 => arndtV c.blocks = c.blocks).card = 1 ∧
    (Finset.univ.filter fun c : Composition 4 => arndtV c.blocks = c.blocks).card = 1 ∧
    (Finset.univ.filter fun c : Composition 2 => arndtV c.blocks = c.blocks).card = 0 ∧
    (Finset.univ.filter fun c : Composition 3 => arndtV c.blocks = c.blocks).card = 0 ∧
    ∀ j : ℕ, 1 ≤ j →
      (Finset.univ.filter fun c : Composition (2 * j) => arndtV c.blocks = c.blocks).card =
          Nat.fib (j - 1) ∧
        (Finset.univ.filter fun c : Composition (2 * j + 1) =>
          arndtV c.blocks = c.blocks).card = Nat.fib (j - 1) := by
  have card_lists (n : ℕ) : (fixedLists n).card = (fixedComps n).card := Finset.card_map _
  obtain ⟨h1, h4, h2, h3⟩ := small_counts
  simp only [card_lists] at h1 h4 h2 h3
  refine ⟨fun _ c => fixed_iff_pattern _ (fun _ => c.blocks_pos), ?_, h1, h4, h2, h3, ?_⟩
  · intro n hn
    change (fixedComps n).card = (fixedComps (n - 2)).card + (fixedComps (n - 4)).card
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [show k + 5 - 2 = k + 3 by omega, show k + 5 - 4 = k + 1 by omega]
    simpa only [card_lists] using count_recurrence k
  · rintro (_ | k) hk
    · omega
    · simpa [card_lists, fixedComps, Nat.mul_succ, Nat.add_assoc] using fib_counts k

end MetaMathlibExt
