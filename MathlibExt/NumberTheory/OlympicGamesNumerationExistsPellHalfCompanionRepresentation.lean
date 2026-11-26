/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.NumberTheory.PellLucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Numeration by Pell and half-companion Pell numbers

This module proves existence of representations with the digit restrictions of Theorem 5.
The proof constructs digits whose partial sums stay below the next place value.

Reference: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 5.
-/

namespace MetaMathlibExt

open Finset

private lemma pell_step (n : ℕ) :
    pellNumber (n + 1) = pellLucasSequence n + pellNumber n ∧
      pellLucasSequence (n + 1) = pellLucasSequence n + 2 * pellNumber n := by
  induction n with
  | zero => decide
  | succ n ih =>
    change pellNumber (n + 2) = pellLucasSequence (n + 1) + pellNumber (n + 1) ∧
      pellLucasSequence (n + 2) = pellLucasSequence (n + 1) + 2 * pellNumber (n + 1)
    rw [pellNumber, pellLucasSequence_succ_succ]
    omega

private lemma pell_bounds (n : ℕ) :
    n ≤ pellNumber n ∧ 1 ≤ pellLucasSequence n ∧ pellNumber n ≤ pellLucasSequence n := by
  induction n with
  | zero => simp [pellNumber]
  | succ n ih =>
    obtain ⟨hp, hh⟩ := pell_step n
    omega

private def place (n : ℕ) : ℕ :=
  if n % 2 = 1 then pellNumber n else pellLucasSequence n

private lemma place_even (k : ℕ) : place (2 * k) = pellLucasSequence (2 * k) := by
  simp [place]

private lemma place_odd (k : ℕ) : place (2 * k + 1) = pellNumber (2 * k + 1) := by
  simp [place, Nat.add_mod]

private lemma place_pos (n : ℕ) : 0 < place n := by
  have hb := pell_bounds n
  dsimp [place]
  split <;> omega

private lemma place_lower (n : ℕ) : n ≤ place n := by
  have hb := pell_bounds n
  dsimp [place]
  split <;> omega

private lemma place_mono : Monotone place := by
  apply monotone_nat_of_le_succ
  intro n
  have hs := pell_step n
  have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hm with hm | hm <;> simp [place, Nat.add_mod, hm] <;> omega

private lemma place_even_step (k : ℕ) :
    place (2 * k + 2) + place (2 * k) = 4 * place (2 * k + 1) := by
  have hp := (pell_step (2 * k)).1
  have hh := (pell_step (2 * k + 1)).2
  have hh' := (pell_step (2 * k)).2
  simp only [Nat.add_assoc, Nat.reduceAdd] at hp hh hh'
  rw [show 2 * k + 2 = 2 * (k + 1) by omega, place_even, place_even, place_odd]
  have heq : 2 * (k + 1) = 2 * k + 2 := by omega
  rw [heq]
  omega

private lemma place_odd_step (k : ℕ) :
    place (2 * k + 3) + place (2 * k + 1) = 2 * place (2 * k + 2) := by
  have hp := (pell_step (2 * k + 2)).1
  have hh := (pell_step (2 * k + 1)).2
  have hp' := (pell_step (2 * k + 1)).1
  simp only [Nat.add_assoc, Nat.reduceAdd] at hp hh hp'
  rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega, place_odd,
    show 2 * k + 2 = 2 * (k + 1) by omega, place_even, place_odd]
  have heq : 2 * (k + 1) = 2 * k + 2 := by omega
  rw [heq]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  omega

private lemma exists_greedy_digits (n t : ℕ) (ht : t < place (n + 1)) :
    ∃ a : ℕ → ℕ, a 0 = 0 ∧ ∀ m, (∑ k ∈ Icc 1 m, a k * place k) < place (m + 1) ∧
      (n ≤ m → (∑ k ∈ Icc 1 m, a k * place k) = t) := by
  induction n generalizing t with
  | zero =>
    have ht0 : t = 0 := by simpa [place, pellNumber] using ht
    refine ⟨fun _ ↦ 0, rfl, fun m ↦ ?_⟩
    simp [ht0, place_pos]
  | succ n ih =>
    obtain ⟨a, ha0, ha⟩ := ih (t % place (n + 1)) (Nat.mod_lt _ (place_pos _))
    refine ⟨fun k ↦ a k + if k = n + 1 then t / place (n + 1) else 0, ?_, fun m ↦ ?_⟩
    · simp [ha0]
    · simp only [Nat.add_mul, ite_mul, Nat.zero_mul, sum_add_distrib, sum_ite_eq', mem_Icc]
      by_cases hnm : n + 1 ≤ m
      · rw [ite_eq_left ⟨by omega, hnm⟩, (ha m).2 (by omega), Nat.mod_add_div']
        exact ⟨ht.trans_le (place_mono (by omega)), fun _ ↦ rfl⟩
      · simp [hnm, (ha m).1]

private lemma greedy_single_lt (a : ℕ → ℕ)
    (ha : ∀ m, (∑ k ∈ Icc 1 m, a k * place k) < place (m + 1))
    (i : ℕ) (hi : 1 ≤ i) : a i * place i < place (i + 1) := by
  exact (single_le_sum (s := Icc 1 i) (f := fun k ↦ a k * place k)
    (fun _ _ ↦ Nat.zero_le _) (by simp only [mem_Icc]; exact ⟨hi, le_rfl⟩)).trans_lt (ha i)

private lemma greedy_pair_lt (a : ℕ → ℕ)
    (ha : ∀ m, (∑ k ∈ Icc 1 m, a k * place k) < place (m + 1))
    (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    a i * place i + a j * place j < place (j + 1) := by
  have hs : a i * place i + a j * place j ≤ ∑ k ∈ Icc 1 j, a k * place k := by
    calc
      _ = ∑ k ∈ {i, j}, a k * place k := (sum_pair hij.ne).symm
      _ ≤ _ := sum_le_sum_of_subset (by
        intro k hk
        simp only [mem_insert, mem_singleton] at hk
        rcases hk with rfl | rfl <;> simp only [mem_Icc] <;> omega)
  exact hs.trans_lt (ha j)

private lemma place_back (k : ℕ) (hk : 1 ≤ k) :
    place (2 * k + 1) + place (2 * k - 1) = 2 * place (2 * k) ∧
      place (2 * k) ≤ 4 * place (2 * k - 1) := by
  have h₁ := place_odd_step (k - 1)
  have h₂ := place_even_step (k - 1)
  have he : 2 * (k - 1) + 2 = 2 * k := by omega
  have ho : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
  have ho' : 2 * (k - 1) + 3 = 2 * k + 1 := by omega
  rw [he, ho, ho'] at h₁
  rw [he, ho] at h₂
  exact ⟨h₁, by omega⟩

private lemma greedy_odd_bound (a : ℕ → ℕ)
    (ha : ∀ m, (∑ k ∈ Icc 1 m, a k * place k) < place (m + 1))
    (k : ℕ) : a (2 * k + 1) ≤ 3 := by
  have hs := greedy_single_lt a ha (2 * k + 1) (by omega)
  have he := place_even_step k
  simp only [Nat.add_assoc, Nat.reduceAdd] at hs
  by_contra h
  have hm := Nat.mul_le_mul_right (place (2 * k + 1)) (by omega : 4 ≤ a (2 * k + 1))
  omega

private lemma greedy_even_bound (a : ℕ → ℕ) (ha0 : a 0 = 0)
    (ha : ∀ m, (∑ k ∈ Icc 1 m, a k * place k) < place (m + 1))
    (k : ℕ) : a (2 * k) ≤ 1 := by
  cases k with
  | zero => simp [ha0]
  | succ k =>
    have hs := greedy_single_lt a ha (2 * k + 2) (by omega)
    have he := place_odd_step k
    have hp := place_pos (2 * k + 1)
    have hi : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [hi]
    simp only [Nat.add_assoc, Nat.reduceAdd] at hs
    by_contra h
    have hm := Nat.mul_le_mul_right (place (2 * k + 2)) (by omega : 2 ≤ a (2 * k + 2))
    omega

private lemma greedy_adjacent_even (a : ℕ → ℕ)
    (ha : ∀ m, (∑ k ∈ Icc 1 m, a k * place k) < place (m + 1))
    (k : ℕ) (hk : 1 ≤ k) (hmax : a (2 * k + 1) = 3) :
    a (2 * k) = 0 ∧ a (2 * k + 2) = 0 := by
  have he := place_even_step k
  have ho := place_odd_step k
  have hb := (place_back k hk).1
  constructor
  · have hs := greedy_pair_lt a ha (2 * k) (2 * k + 1) (by omega) (by omega)
    rw [hmax] at hs
    simp only [Nat.add_assoc, Nat.reduceAdd] at hs
    by_contra h
    have hm := Nat.mul_le_mul_right (place (2 * k)) (by omega : 1 ≤ a (2 * k))
    omega
  · have hs := greedy_pair_lt a ha (2 * k + 1) (2 * k + 2) (by omega) (by omega)
    rw [hmax] at hs
    simp only [Nat.add_assoc, Nat.reduceAdd] at hs
    by_contra h
    have hm := Nat.mul_le_mul_right (place (2 * k + 2)) (by omega : 1 ≤ a (2 * k + 2))
    omega

private lemma greedy_previous_odd (a : ℕ → ℕ)
    (ha : ∀ m, (∑ k ∈ Icc 1 m, a k * place k) < place (m + 1))
    (k : ℕ) (hk : 1 ≤ k) (hmax : a (2 * k + 1) = 3) :
    a (2 * k - 1) < 3 := by
  have hs := greedy_pair_lt a ha (2 * k - 1) (2 * k + 1) (by omega) (by omega)
  have he := place_even_step k
  have hb := place_back k hk
  rw [hmax] at hs
  simp only [Nat.add_assoc, Nat.reduceAdd] at hs
  by_contra h
  have hm := Nat.mul_le_mul_right (place (2 * k - 1)) (by omega : 3 ≤ a (2 * k - 1))
  omega

private lemma exists_place_interval (t : ℕ) (ht : 0 < t) :
    ∃ n, 1 ≤ n ∧ place n ≤ t ∧ t < place (n + 1) := by
  have hex : ∃ m, t < place m :=
    ⟨t + 1, (Nat.lt_succ_self t).trans_le (place_lower (t + 1))⟩
  let m := Nat.find hex
  have hhi : t < place m := Nat.find_spec hex
  have hm : 2 ≤ m := by
    by_contra h
    have hm' : m = 0 ∨ m = 1 := by omega
    rcases hm' with hm' | hm' <;> simp [hm', place, pellNumber] at hhi <;> omega
  have hlo : place (m - 1) ≤ t :=
    Nat.le_of_not_gt (Nat.find_min hex (by omega : m - 1 < Nat.find hex))
  refine ⟨m - 1, by omega, hlo, ?_⟩
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ m)] using hhi

private lemma greedy_constraints (a : ℕ → ℕ) (ha0 : a 0 = 0)
    (ha : ∀ m, (∑ k ∈ Icc 1 m, a k * place k) < place (m + 1)) :
    a 1 ≤ 2 ∧ (a 1 = 2 → a 2 = 0) ∧ (∀ k, a (2 * k + 1) ≤ 3 ∧ a (2 * k) ≤ 1) ∧
      (∀ k, 1 ≤ k → a (2 * k + 1) = 3 → a (2 * k) = 0 ∧ a (2 * k + 2) = 0) ∧
      (∀ k, 1 ≤ k → a (2 * k + 1) = 3 → a (2 * k - 1) < 3 ∧ a (2 * k + 3) < 3) := by
  refine ⟨?_, ?_, fun k ↦ ⟨greedy_odd_bound a ha k, greedy_even_bound a ha0 ha k⟩,
    greedy_adjacent_even a ha, ?_⟩
  · have hs := greedy_single_lt a ha 1 le_rfl
    have hs' : a 1 < 3 := by simpa [place, pellNumber, pellLucasSequence] using hs
    omega
  · intro hmax
    have hs := greedy_pair_lt a ha 1 2 le_rfl (by decide)
    simp [place, pellNumber, pellLucasSequence, hmax] at hs
    omega
  · intro k hk hmax
    refine ⟨greedy_previous_odd a ha k hk hmax, ?_⟩
    have hbound := greedy_odd_bound a ha (k + 1)
    have hi : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    rw [hi] at hbound
    by_contra h
    have hm : a (2 * (k + 1) + 1) = 3 := by rw [hi]; omega
    have hp := greedy_previous_odd a ha (k + 1) (by omega) hm
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, hmax] at hp
    omega

@[expose] public section

/-- **Numeration by Pell and half-companion Pell numbers.** Let $P_n$ be the Pell numbers
($P_0 = 0$, $P_1 = 1$, $P_{n+2} = 2P_{n+1} + P_n$) and $H_n$ the half-companion Pell numbers
($H_0 = H_1 = 1$, $H_{n+2} = 2H_{n+1} + H_n$), and let $R_k = P_k$ for odd $k$ and
$R_k = H_k$ for even $k$. Then for every positive integer $t$ there are a natural number $n \ge 1$
and natural numbers $a_0, a_1, a_2, \dots$ such that $R_n \le t < R_{n+1}$,
$t = \sum_{k=1}^{n} a_k R_k$, $a_1 \le 2$, $a_2 = 0$ if $a_1 = 2$, $a_{2k+1} \le 3$ and
$a_{2k} \le 1$ for every $k \ge 0$, and for every $k \ge 1$ with $a_{2k+1} = 3$ we have
$a_{2k} = a_{2k+2} = 0$, $a_{2k-1} < 3$ and $a_{2k+3} < 3$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 5. -/
theorem exists_pell_halfCompanion_representation (R : ℕ → ℕ)
    (hR : ∀ k, R k = if k % 2 = 1 then pellNumber k else pellLucasSequence k)
    {t : ℕ} (ht : 0 < t) :
    ∃ (n : ℕ) (a : ℕ → ℕ), 1 ≤ n ∧ R n ≤ t ∧ t < R (n + 1) ∧
      t = ∑ k ∈ Icc 1 n, a k * R k ∧
      a 1 ≤ 2 ∧ (a 1 = 2 → a 2 = 0) ∧ (∀ k, a (2 * k + 1) ≤ 3 ∧ a (2 * k) ≤ 1) ∧
      (∀ k, 1 ≤ k → a (2 * k + 1) = 3 → a (2 * k) = 0 ∧ a (2 * k + 2) = 0) ∧
      (∀ k, 1 ≤ k → a (2 * k + 1) = 3 → a (2 * k - 1) < 3 ∧ a (2 * k + 3) < 3)
    := by
  have hR' : R = place := funext hR
  subst R
  obtain ⟨n, hn, hlo, hhi⟩ := exists_place_interval t ht
  obtain ⟨a, ha0, ha⟩ := exists_greedy_digits n t hhi
  exact ⟨n, a, hn, hlo, hhi, ((ha n).2 le_rfl).symm,
    greedy_constraints a ha0 (fun m ↦ (ha m).1)⟩

end

end MetaMathlibExt
