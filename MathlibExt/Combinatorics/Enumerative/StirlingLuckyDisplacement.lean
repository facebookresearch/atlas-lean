/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.OfFn
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

private theorem pref_val_add_one {n : ℕ} {w : Fin (2 * n) → ℕ}
    (hw : IsStirlingPermutation n w) (i : Fin (2 * n)) : (stirlingPref w i).val + 1 = w i := by
  obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp (hw.1 i)
  simp only [stirlingPref, Nat.mod_eq_of_lt (show w i - 1 < 2 * n by omega)]
  omega

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

end

end MetaMathlibExt
