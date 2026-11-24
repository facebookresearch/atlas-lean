/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Order.Interval.Finset.Fin
public import MathlibExt.Combinatorics.Enumerative.LuckyCars
public import MathlibExt.Combinatorics.Enumerative.StirlingPermutation

/-!
# Lucky and displacement statistics of Stirling permutations

This file follows L. Colmenarejo, A. Dawkins, J. Elder, P. E. Harris, K. J. Harry,
S. Kara, D. Smith, and B. E. Tenner, *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7
(arXiv:2403.03280).

A Stirling permutation of order `n` is MathlibExt's
`MetaMathlibExt.IsStirlingPermutation n w` for a word `w : Fin (2 * n) → ℕ`
(`w(1) ⋯ w(2n)` is `w 0, …, w (2n-1)`). It is read as a parking function of
length `2n`: car `i + 1` prefers spot `w i`. Parking is the existing greedy
outcome `MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted.parkSpots`
(zero-based), applied to the zero-based preferences `stirlingPref w`. Car and
spot numbers in the statements below are the paper's one-based numbers: the car
at index `i : Fin (2 * n)` is car `i + 1`, and `stirlingParkSpot w i` is its
one-based spot `p(i + 1)`.
-/

open MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted (parkSpots)

namespace MetaMathlibExt

@[expose] public section

/-- **Zero-based preferences of a word.** Let $w = w_1 \cdots w_{2n}$ be a word of natural
numbers, read as the preferences of $2n$ cars for spots numbered $0, \dots, 2n - 1$. Car
$i \in \{1, \dots, 2n\}$ prefers the spot $(w_i - 1) \bmod 2n$, where $w_i - 1$ is truncated at
$0$. When every $w_i$ lies in $\{1, \dots, 2n\}$, for example when $w$ is a Stirling permutation
of order $n$, this is the spot $w_i - 1$, which is spot $w_i$ in the one-based numbering.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Section 1 (Stirling permutations read as parking functions of length `2n`). -/
public def stirlingPref {n : ℕ} (w : Fin (2 * n) → ℕ) (i : Fin (2 * n)) : Fin (2 * n) :=
  ⟨(w i - 1) % (2 * n), Nat.mod_lt _ i.pos⟩

/-- **Parking spot of a car.** Let $w = w_1 \cdots w_{2n}$ be a word of natural numbers. Car $i$
prefers spot $q_i = ((w_i - 1) \bmod 2n) + 1$, where $w_i - 1$ is truncated at $0$; when every
$w_i$ lies in $\{1, \dots, 2n\}$, this is $q_i = w_i$. Cars $1, \dots, 2n$ arrive in order, and
car $i$ parks in the least spot $p(i) \in \{q_i, \dots, 2n\}$ not taken by an earlier car, or in
$p(i) = q_i$ if there is no such spot. The parking spot of car $i \in \{1, \dots, 2n\}$ is $p(i)$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 5.1. -/
public def stirlingParkSpot {n : ℕ} (w : Fin (2 * n) → ℕ) (i : Fin (2 * n)) : ℕ :=
  (parkSpots (stirlingPref w) i).val + 1

/-- **The lucky set of a word.** Let $w = w_1 \cdots w_{2n}$ be a word of natural numbers. Car
$i$ prefers spot $q_i = ((w_i - 1) \bmod 2n) + 1$, where $w_i - 1$ is truncated at $0$; when
every $w_i$ lies in $\{1, \dots, 2n\}$, this is $q_i = w_i$. Cars $1, \dots, 2n$ arrive in
order, and car $i$ parks in the least spot $p(i) \in \{q_i, \dots, 2n\}$ not taken by an
earlier car, or in $p(i) = q_i$ if there is no such spot. The lucky set $\mathrm{Lucky}(w)$
is the set of cars $i \in \{1, \dots, 2n\}$ with $p(i) = w_i$; when every $w_i$ lies in
$\{1, \dots, 2n\}$, these are the cars that park in their preferred spot.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 1.2. -/
public def stirlingLuckySet {n : ℕ} (w : Fin (2 * n) → ℕ) : Finset ℕ :=
  (Finset.univ.filter fun i => stirlingParkSpot w i = w i).image fun i => i.val + 1

/-- **Displacement of a car.** Let $w = w_1 \cdots w_{2n}$ be a word of natural numbers. Car
$i$ prefers spot $q_i = ((w_i - 1) \bmod 2n) + 1$, where $w_i - 1$ is truncated at $0$; when
every $w_i$ lies in $\{1, \dots, 2n\}$, this is $q_i = w_i$. Cars $1, \dots, 2n$ arrive in
order, and car $i$ parks in the least spot $p(i) \in \{q_i, \dots, 2n\}$ not taken by an
earlier car, or in $p(i) = q_i$ if there is no such spot. The displacement of car $i$ is
$d(i) = p(i) - w_i$, where the subtraction is truncated at $0$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 5.1; the tuple `i ↦ d(i + 1)` is the displacement composition
`dis(w)` (Definition 5.4). -/
public def stirlingDisplacement {n : ℕ} (w : Fin (2 * n) → ℕ) (i : Fin (2 * n)) : ℕ :=
  stirlingParkSpot w i - w i

/-- **Total displacement of a word.** Let $w = w_1 \cdots w_{2n}$ be a word of natural numbers,
and for $i \in \{1, \dots, 2n\}$ let $d(i)$ be the displacement of car $i$ in $w$. The total
displacement of $w$ is $d(w) = \sum_{i=1}^{2n} d(i)$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 5.1. -/
public def stirlingTotalDisplacement {n : ℕ} (w : Fin (2 * n) → ℕ) : ℕ :=
  ∑ i, stirlingDisplacement w i

/-- **Admissible lucky sets.** Let $n$ be a natural number. A finite set $S$ of natural numbers
is an $n$-admissible lucky set if $S = \mathrm{Lucky}(w)$ for some Stirling permutation $w$ of
order $n$, where $\mathrm{Lucky}(w)$ is the set of lucky cars of $w$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 3.1. -/
public def IsAdmissibleLuckySet (n : ℕ) (S : Finset ℕ) : Prop :=
  ∃ w : Fin (2 * n) → ℕ, IsStirlingPermutation n w ∧ stirlingLuckySet w = S

/-- **Lucky sets of 1122 and 1221.** Read as parking functions of length $4$, the Stirling
permutation $1122$ has car $1$ as its only lucky car, and $1221$ has exactly cars $1$ and $2$
lucky: $\mathrm{Lucky}(1122) = \{1\}$ and $\mathrm{Lucky}(1221) = \{1, 2\}$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definitions 1.2 and 3.1. -/
public theorem stirlingLuckySet_small :
    stirlingLuckySet (n := 2) ![1, 1, 2, 2] = {1} ∧
      stirlingLuckySet (n := 2) ![1, 2, 2, 1] = {1, 2} := by
  decide

/-- **Displacement compositions of 1122 and 11244233.** The displacement composition of a word
$w = w_1 \cdots w_{2n}$ is $\mathrm{dis}(w) = (d(1), \dots, d(2n))$, where $d(i)$ is the
displacement of car $i$. For the Stirling permutations $1122$ of order $2$ and $11244233$ of
order $4$, $\mathrm{dis}(1122) = (0, 1, 1, 2)$ and
$\mathrm{dis}(11244233) = (0, 1, 1, 0, 1, 4, 4, 5)$ (the paper's Example 5.5).

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 5.4 and Example 5.5. -/
public theorem stirlingDisplacement_small :
    (fun i => stirlingDisplacement (n := 2) ![1, 1, 2, 2] i) = ![0, 1, 1, 2] ∧
      (fun i => stirlingDisplacement (n := 4) ![1, 1, 2, 4, 4, 2, 3, 3] i) =
        ![0, 1, 1, 0, 1, 4, 4, 5] := by
  decide

namespace IsAdmissibleLuckySet

open MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

private theorem nextFreeSpot_of_notMem {m : ℕ} {occ : Finset (Fin m)} {a : Fin m}
    (ha : a ∉ occ) : nextFreeSpot occ a = a := by
  have hmem : a ∈ Finset.univ.filter (fun q : Fin m => a ≤ q ∧ q ∉ occ) := by simp [ha]
  have h := Finset.min'_mem _ ⟨a, hmem⟩
  rw [nextFreeSpot, dite_eq_left ⟨a, hmem⟩]
  exact le_antisymm (Finset.min'_le _ _ hmem) (Finset.mem_filter.mp h).2.1

private theorem parkSpots_first {m : ℕ} (f : Fin m → Fin m) (i : Fin m) (hi : i.val = 0) :
    parkSpots f i = f i := by
  cases m with
  | zero => exact i.elim0
  | succ m =>
    obtain rfl : i = 0 := Fin.ext hi
    simp [parkSpots, List.ofFn_succ, parkSpotsFrom, nextFreeSpot_of_notMem]

/-- If each spot up to the last preference is occupied or requested in the prefix, and at
least one spot will still be free, the last car parks away from its preference. -/
private theorem parkSpotsFrom_last_ne {m : ℕ} (l : List (Fin m)) (occ : Finset (Fin m))
    (a d : Fin m) (hcard : occ.card + l.length < m)
    (hcover : ∀ q ≤ a, q ∈ occ ∨ q ∈ l) :
    (parkSpotsFrom (l ++ [a]) occ).getD l.length d ≠ a := by
  induction l generalizing occ with
  | nil =>
    have hfull (q : Fin m) (hq : q ≤ a) : q ∈ occ := by simpa using hcover q hq
    have hne : occ ≠ Finset.univ := by
      intro heq
      simp [heq] at hcard
    obtain ⟨q, hq⟩ : ∃ q, q ∉ occ := by simpa [Finset.eq_univ_iff_forall] using hne
    have hfree : (Finset.univ.filter (fun q : Fin m => a ≤ q ∧ q ∉ occ)).Nonempty :=
      ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_ge (fun h => hq (hfull q h)), hq⟩⟩
    simp only [List.nil_append, parkSpotsFrom, List.length_nil, List.getD_cons_zero, nextFreeSpot,
      dite_eq_left hfree]
    intro heq
    have hnot := (Finset.mem_filter.mp (Finset.min'_mem _ hfree)).2.2
    rw [heq] at hnot
    exact hnot (hfull a le_rfl)
  | cons b l ih =>
    have hb : b ∈ insert (nextFreeSpot occ b) occ := by
      by_cases h : b ∈ occ
      · exact Finset.mem_insert_of_mem h
      · simp [nextFreeSpot_of_notMem h]
    apply ih
    · have := Finset.card_insert_le (nextFreeSpot occ b) occ
      simp only [List.length_cons] at hcard
      omega
    · intro q hq
      rcases hcover q hq with h | h
      · exact Or.inl (Finset.mem_insert_of_mem h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl hb
        · exact Or.inr h

private theorem parkSpots_last_ne {m : ℕ} (f : Fin m → Fin m) (i : Fin m)
    (hi : i.val + 1 = m) (hcover : ∀ q ≤ f i, ∃ j < i, f j = q) : parkSpots f i ≠ f i := by
  cases m with
  | zero => exact i.elim0
  | succ m =>
    obtain rfl : i = Fin.last m := Fin.ext (by simpa using hi)
    rw [parkSpots, List.ofFn_succ', List.concat_eq_append]
    let l := List.ofFn (fun j : Fin m => f j.castSucc)
    have hmem (q : Fin (m + 1)) (hq : q ≤ f (Fin.last m)) : q ∈ l := by
      obtain ⟨j, hj, rfl⟩ := hcover q hq
      exact List.mem_ofFn.mpr ⟨⟨j.val, hj⟩, rfl⟩
    simpa only [l, List.length_ofFn, Fin.val_last] using
      parkSpotsFrom_last_ne l ∅ (f (Fin.last m)) (Fin.last m) (by simp [l])
        (fun q hq => Or.inr (hmem q hq))

private theorem pref_val_add_one_of_mem {n : ℕ} {w : Fin (2 * n) → ℕ}
    (i : Fin (2 * n)) (hi : w i ∈ Finset.Icc 1 n) : (stirlingPref w i).val + 1 = w i := by
  obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hi
  simp only [stirlingPref, Nat.mod_eq_of_lt (show w i - 1 < 2 * n by omega)]
  omega

private theorem pref_val_add_one {n : ℕ} {w : Fin (2 * n) → ℕ}
    (hw : IsStirlingPermutation n w) (i : Fin (2 * n)) : (stirlingPref w i).val + 1 = w i :=
  pref_val_add_one_of_mem i (hw.1 i)

/-- **Necessary conditions for admissible lucky sets.** Let $n \ge 1$. If $S$ is an
$n$-admissible lucky set, then $1 \in S$ and $2n \notin S$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Corollary 3.4 (`jis-2024-24.6.7-cor-24`). -/
public theorem one_mem_and_two_mul_not_mem (n : ℕ) (hn : 1 ≤ n)
    (S : Finset ℕ) (hS : IsAdmissibleLuckySet n S) : 1 ∈ S ∧ 2 * n ∉ S := by
  obtain ⟨w, hw, rfl⟩ := hS
  constructor
  · let i : Fin (2 * n) := ⟨0, by omega⟩
    refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    rw [stirlingParkSpot, parkSpots_first _ i rfl, pref_val_add_one hw]
  · intro h
    obtain ⟨i, hi, hlast⟩ := Finset.mem_image.mp h
    have hlucky := (Finset.mem_filter.mp hi).2
    have hpref := pref_val_add_one hw i
    rw [stirlingParkSpot, ← hpref] at hlucky
    apply parkSpots_last_ne (stirlingPref w) i hlast _ (Fin.ext (Nat.succ.inj hlucky))
    intro q hq
    -- Each letter occurs twice, so deleting the last car leaves every preference represented.
    have hbound := (Finset.mem_Icc.mp (hw.1 i)).2
    have hletter : q.val + 1 ∈ Finset.Icc 1 n := by
      change q.val ≤ (stirlingPref w i).val at hq
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    obtain ⟨j, hj, hne⟩ := Finset.exists_mem_ne (by rw [hw.2.1 _ hletter]; decide) i
    have hbefore : j < i := lt_of_le_of_ne (Fin.le_def.mpr (by have := j.isLt; omega)) hne
    refine ⟨j, hbefore, Fin.ext (Nat.succ.inj ?_)⟩
    exact (pref_val_add_one hw j).trans (Finset.mem_filter.mp hj).2

end IsAdmissibleLuckySet

/-- **Left-to-right minima of a Stirling permutation sit at odd positions.** Let
$w = w_1 \cdots w_{2n}$ be a Stirling permutation of order $n$ and let $j \in \{1, \dots, 2n\}$.
If $w_j < w_i$ for every $i < j$, then $j$ is odd.

In the paper, $j$ is the first car preferring spot $w_j$; the hypothesis $w_j < w_i$ for all
$i < j$ already implies this, and $w_j \in \{1, \dots, n\}$ holds for every Stirling permutation.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 3.7 (`jis-2024-24.6.7-lem-27`). -/
public theorem stirling_odd_of_lt_all_before (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (j : Fin (2 * n)) (hj : ∀ i < j, w j < w i) :
    Odd (j.val + 1) := by
  -- Every letter in the prefix has both of its occurrences there.
  have pairs (v : ℕ) (hv : v ∈ (Finset.Iio j).image w) :
      ((Finset.Iio j).filter fun k => w k = v).card = 2 := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    have hij := Finset.mem_Iio.mp hi
    have hfilter : (Finset.Iio j).filter (fun k => w k = w i) =
        Finset.univ.filter (fun k => w k = w i) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Iio, Finset.mem_univ, true_and,
        and_iff_right_iff_imp]
      intro hk
      rcases lt_trichotomy k j with h | rfl | h
      · exact h
      · exact ((hj i hij).ne hk).elim
      · exact ((hj i hij).asymm (hw.2.2 _ (hw.1 i) i j k hij h rfl hk)).elim
    rw [hfilter]
    exact hw.2.1 _ (hw.1 i)
  have hcard := (Finset.card_eq_sum_card_image w (Finset.Iio j)).trans (Finset.sum_const_nat pairs)
  rw [Fin.card_Iio, Nat.mul_comm _ 2] at hcard
  exact ⟨_, congrArg (· + 1) hcard⟩

namespace stirlingTotalDisplacement_eq

open MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

/-- Each greedy outcome is at least the corresponding preference. -/
private theorem prefs_le_spots {m : ℕ} (l : List (Fin m)) (occ : Finset (Fin m)) :
    List.Forall₂ (· ≤ ·) l (parkSpotsFrom l occ) := by
  induction l generalizing occ with
  | nil => exact .nil
  | cons a l ih =>
    refine .cons ?_ (ih _)
    unfold nextFreeSpot
    split
    · rename_i hfree
      exact (Finset.mem_filter.mp (Finset.min'_mem _ hfree)).2.1
    · exact le_rfl

/-- A missing spot was never requested. If every car could have used it, each car
occupies a fresh spot, so fewer than a full lot of spots have been taken. -/
private theorem missing_spot {m : ℕ} (q : Fin m) (l : List (Fin m)) (occ : Finset (Fin m))
    (hq : q ∉ occ) (hmiss : q ∉ parkSpotsFrom l occ) :
    q ∉ l ∧ ((∀ a ∈ l, a ≤ q) → occ.card + l.length < m) := by
  induction l generalizing occ with
  | nil => simpa using Finset.card_lt_univ_of_notMem hq
  | cons a l ih =>
    simp only [parkSpotsFrom, List.mem_cons, not_or] at hmiss
    obtain ⟨hhead, htail⟩ := hmiss
    obtain ⟨hn, hcard⟩ := ih (insert (nextFreeSpot occ a) occ) (by simp [hhead, hq]) htail
    constructor
    · simp only [List.mem_cons, not_or]
      refine ⟨?_, hn⟩
      rintro rfl
      exact hhead (IsAdmissibleLuckySet.nextFreeSpot_of_notMem hq).symm
    · intro hle
      have ha : a ≤ q := hle a List.mem_cons_self
      have hfree : (Finset.univ.filter (fun s : Fin m => a ≤ s ∧ s ∉ occ)).Nonempty :=
        ⟨q, by simp [ha, hq]⟩
      have hfresh : nextFreeSpot occ a ∉ occ := by
        rw [nextFreeSpot, dite_eq_left hfree]
        exact (Finset.mem_filter.mp (Finset.min'_mem _ hfree)).2.2
      specialize hcard (fun b hb => hle b (List.mem_cons_of_mem _ hb))
      rw [Finset.card_insert_of_notMem hfresh] at hcard
      simp only [List.length_cons]
      omega

/-- Every low spot is requested, and every higher spot is reachable by every car. -/
private theorem spots_surjective_of_cover {n : ℕ} {w : Fin (2 * n) → ℕ}
    (hbound : ∀ i, w i ∈ Finset.Icc 1 n)
    (hcover : ∀ v ∈ Finset.Icc 1 n, ∃ i, w i = v) :
    Function.Surjective (parkSpots (stirlingPref w)) := by
  let prefs := List.ofFn (stirlingPref w)
  have hlen : (parkSpotsFrom prefs ∅).length = 2 * n := by
    rw [← (prefs_le_spots prefs ∅).length_eq, List.length_ofFn]
  intro q
  have hmem : q ∈ parkSpotsFrom prefs ∅ := by
    by_contra hmiss
    obtain ⟨hn, hcard⟩ := missing_spot q prefs ∅ (by simp) hmiss
    by_cases hlow : q.val < n
    · have hq : q.val + 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      obtain ⟨i, hi⟩ := hcover _ hq
      apply hn (List.mem_ofFn.mpr ⟨i, Fin.ext (Nat.succ.inj ?_)⟩)
      exact (IsAdmissibleLuckySet.pref_val_add_one_of_mem i (hbound i)).trans hi
    · apply Nat.lt_irrefl (2 * n)
      simpa [prefs] using hcard (List.forall_mem_ofFn_iff.mpr (fun i => by
        have := IsAdmissibleLuckySet.pref_val_add_one_of_mem i (hbound i)
        have := (Finset.mem_Icc.mp (hbound i)).2
        change (stirlingPref w i).val ≤ q.val
        omega))
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hmem
  refine ⟨⟨i, hlen ▸ hi⟩, ?_⟩
  exact (List.getD_eq_getElem _ _ hi).trans heq

private theorem letters_covered {n : ℕ} {w : Fin (2 * n) → ℕ}
    (hw : IsStirlingPermutation n w) (v : ℕ) (hv : v ∈ Finset.Icc 1 n) : ∃ i, w i = v := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [hw.2.1 v hv]; decide)
  exact ⟨i, (Finset.mem_filter.mp hi).2⟩

private theorem spots_surjective {n : ℕ} {w : Fin (2 * n) → ℕ} (hw : IsStirlingPermutation n w) :
    Function.Surjective (parkSpots (stirlingPref w)) :=
  spots_surjective_of_cover hw.1 (letters_covered hw)

/-- The sum of preferences plus total displacement is the sum of all spots. -/
private theorem displacement_balance {n : ℕ} {w : Fin (2 * n) → ℕ}
    (hbound : ∀ i, w i ∈ Finset.Icc 1 n)
    (hcover : ∀ v ∈ Finset.Icc 1 n, ∃ i, w i = v) :
    stirlingTotalDisplacement w + ∑ i, w i = ∑ i : Fin (2 * n), (1 + i.val) := by
  have hpair := prefs_le_spots (List.ofFn (stirlingPref w)) ∅
  have hle (i : Fin (2 * n)) : w i ≤ stirlingParkSpot w i := by
    have hi : i.val < (List.ofFn (stirlingPref w)).length := by simp
    have hj := hpair.length_eq ▸ hi
    have h := hpair.get hi hj
    simp only [List.get_eq_getElem, List.getElem_ofFn, Fin.eta] at h
    rw [← IsAdmissibleLuckySet.pref_val_add_one_of_mem i (hbound i), stirlingParkSpot,
      parkSpots, List.getD_eq_getElem _ _ hj]
    exact Nat.succ_le_succ h
  calc
    stirlingTotalDisplacement w + ∑ i, w i = ∑ i, stirlingParkSpot w i := by
      unfold stirlingTotalDisplacement stirlingDisplacement
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i)
    _ = ∑ i : Fin (2 * n), (1 + i.val) := by
      let e := Equiv.ofBijective _ (Finite.surjective_iff_bijective.mp
        (spots_surjective_of_cover hbound hcover))
      have sum_spots := e.sum_comp (fun i : Fin (2 * n) => 1 + i.val)
      change (∑ i, (1 + (parkSpots (stirlingPref w) i).val)) = _ at sum_spots
      simpa only [stirlingParkSpot, Nat.add_comm _ 1] using sum_spots

end stirlingTotalDisplacement_eq

/-- **Total displacement of a Stirling permutation.** Let $w = w_1 \cdots w_{2n}$ be a Stirling
permutation of order $n$, read as a parking function of length $2n$. Then the total displacement
of $w$, the sum $d(1) + \dots + d(2n)$ of the displacements of its cars, is $n^2$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Corollary 5.3 (`jis-2024-24.6.7-cor-38`). -/
public theorem stirlingTotalDisplacement_eq (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) : stirlingTotalDisplacement w = n ^ 2 := by
  have balance := stirlingTotalDisplacement_eq.displacement_balance hw.1
    (stirlingTotalDisplacement_eq.letters_covered hw)
  -- Group the preferences by letter, each of which occurs twice.
  have hpref : ∑ i, w i = 2 * ∑ j ∈ Finset.range n, (1 + j) := calc
    ∑ i, w i = ∑ v ∈ Finset.Icc 1 n, ∑ i : Fin (2 * n) with w i = v, v :=
      (Finset.sum_fiberwise_of_maps_to' (fun i _ => hw.1 i) id).symm
    _ = 2 * ∑ v ∈ Finset.Icc 1 n, v := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v hv => by simp [hw.2.1 v hv]
    _ = _ := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range (fun v => v)]
      simp
  -- Split the occupied spots into two blocks of length n. Corresponding spots differ by n.
  have hsplit := Finset.sum_range_add (fun j => 1 + j) n n
  rw [← two_mul] at hsplit
  rw [Fin.sum_univ_eq_sum_range, hsplit, hpref] at balance
  simp_rw [← Nat.add_left_comm n 1] at balance
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_id] at balance
  rw [sq]
  omega

/-- **Total displacement of a Stirling permutation is invariant under rearrangement.** Let
$w = w_1 \cdots w_{2n}$ be a Stirling permutation of order $n$ and let $\sigma$ be a permutation
of $\{1, \dots, 2n\}$. Read words of length $2n$ as parking functions, and let $d(v)$ denote the
total displacement of a word $v$, the sum of the displacements of its cars. Then the rearranged
word $w \circ \sigma = w_{\sigma(1)} \cdots w_{\sigma(2n)}$ satisfies $d(w \circ \sigma) = d(w)$.

The rearranged word $w \circ \sigma$ need not be a Stirling permutation.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 37 (`jis-2024-24.6.7-lem-37`; Lemma 5.2 in arXiv:2403.03280v1), quoting
Elder, Harris, Kretschmann, and Martínez Mori, Lemma 3.1. -/
public theorem stirlingTotalDisplacement_comp_perm (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (σ : Equiv.Perm (Fin (2 * n))) :
    stirlingTotalDisplacement (w ∘ σ) = stirlingTotalDisplacement w := by
  have hcover := stirlingTotalDisplacement_eq.letters_covered hw
  have original := stirlingTotalDisplacement_eq.displacement_balance hw.1 hcover
  -- Rearrangement preserves the range of preferences, not necessarily the Stirling condition.
  have rearranged := stirlingTotalDisplacement_eq.displacement_balance (w := w ∘ σ)
    (fun i => hw.1 (σ i)) (fun v hv => by
      obtain ⟨i, hi⟩ := hcover v hv
      exact ⟨σ.symm i, by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi⟩)
  change stirlingTotalDisplacement (w ∘ σ) + (∑ i, w (σ i)) = _ at rearranged
  rw [Equiv.sum_comp σ w] at rearranged
  exact Nat.add_right_cancel (rearranged.trans original.symm)

/-- **Number of cars with zero displacement.** Let $n \ge 1$ and let $w$ be a Stirling
permutation of order $n$, read as a parking function of length $2n$. The number of cars
$i \in \{1, \dots, 2n\}$ with displacement $d(i) = 0$ is at least $1$ and at most $n$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Corollary 5.6 (`jis-2024-24.6.7-cor-41`). -/
public theorem stirling_card_zero_displacement (n : ℕ) (hn : 1 ≤ n) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) :
    1 ≤ (Finset.univ.filter fun i => stirlingDisplacement w i = 0).card ∧
      (Finset.univ.filter fun i => stirlingDisplacement w i = 0).card ≤ n := by
  constructor
  · let first : Fin (2 * n) := ⟨0, by omega⟩
    apply Finset.card_pos.mpr
    refine ⟨first, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [stirlingDisplacement, stirlingParkSpot, IsAdmissibleLuckySet.parkSpots_first _ first rfl,
      IsAdmissibleLuckySet.pref_val_add_one hw, Nat.sub_self]
  · -- Distinct cars with zero displacement occupy distinct spots in the first half of the lot.
    have hinj := Finite.injective_iff_surjective.mpr
      (stirlingTotalDisplacement_eq.spots_surjective hw)
    calc
      _ ≤ (Finset.range n).card := by
        apply Finset.card_le_card_of_injOn (fun i => (parkSpots (stirlingPref w) i).val)
        · intro i hi
          have hle : stirlingParkSpot w i ≤ w i :=
            Nat.sub_eq_zero_iff_le.mp (Finset.mem_filter.mp hi).2
          exact Finset.mem_range.mpr (hle.trans (Finset.mem_Icc.mp (hw.1 i)).2)
        · exact (Fin.val_injective.comp hinj).injOn
      _ = n := Finset.card_range n

end

end MetaMathlibExt
