/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.KArndtRecurrence
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring

/-!
# Arndt compositions with negative even shift

The generalized Arndt count at shift `-2j` equals the number of compositions into odd parts
or even parts at most `2j`, by comparing their recurrences.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Compositions into odd or small even parts.** For natural numbers $k$ and $n$, $c^{2k}_o(n)$
is the number of compositions of $n$, with any number of parts, in which every part is odd or at
most $2k$. For $k = 0$ these are De Morgan's compositions of $n$ into odd parts.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Definitions 2 and 5. -/
def oddOrSmallEvenCompositionCount (k n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), ((Finset.Nat.antidiagonalTuple m n).filter fun c =>
    ∀ i, 0 < c i ∧ (Odd (c i) ∨ c i ≤ 2 * k)).card

/-- **Compositions of five into odd or small even parts.** Let $c^{2k}_o(n)$ be the number of
compositions of $n$ in which every part is odd or at most $2k$. Then $c^0_o(5) = 5$ and
$c^2_o(5) = 14$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Table 3 and the discussion after Theorem 5. -/
theorem oddOrSmallEvenCompositionCount_five :
    oddOrSmallEvenCompositionCount 0 5 = 5 ∧ oddOrSmallEvenCompositionCount 1 5 = 14 := by
  decide

end

namespace kArndtTotalCount_neg_even

open Finset PowerSeries

private abbrev allowed (j a : ℕ) : Prop := 0 < a ∧ (Odd a ∨ a ≤ 2 * j)

private def tuples (j m n : ℕ) : Finset (Fin m → ℕ) :=
  (Nat.antidiagonalTuple m n).filter fun c => ∀ i, allowed j (c i)

private lemma tuples_succ (j m n : ℕ) :
    (tuples j (m + 1) n).card =
      ∑ p ∈ antidiagonal n, if allowed j p.1 then (tuples j m p.2).card else 0 := by
  classical
  let pieces := ((antidiagonal n).filter fun p => allowed j p.1).sigma
    fun p => tuples j m p.2
  let join (z : Σ _ : ℕ × ℕ, Fin m → ℕ) : Fin (m + 1) → ℕ := Fin.cons z.1.1 z.2
  let split (c : Fin (m + 1) → ℕ) : Σ _ : ℕ × ℕ, Fin m → ℕ :=
    ⟨(c 0, ∑ i, Fin.tail c i), Fin.tail c⟩
  have mem_pieces (p : ℕ × ℕ) (c : Fin m → ℕ) :
      (⟨p, c⟩ : Σ _ : ℕ × ℕ, Fin m → ℕ) ∈ pieces ↔
        p.1 + p.2 = n ∧ allowed j p.1 ∧ (∑ i, c i) = p.2 ∧ ∀ i, allowed j (c i) := by
    simp [pieces, tuples, Nat.mem_antidiagonalTuple, and_assoc]
  calc
    _ = pieces.card := by
      apply card_nbij' split join
      · intro c hc
        obtain ⟨hs, hv⟩ := mem_filter.mp hc
        rw [Nat.mem_antidiagonalTuple, Fin.sum_univ_succ] at hs
        exact (mem_pieces _ _).mpr ⟨hs, hv 0, rfl, fun i => hv i.succ⟩
      · rintro ⟨p, c⟩ hz
        obtain ⟨hp, ha, hs, hv⟩ := (mem_pieces _ _).mp hz
        exact mem_filter.mpr
          ⟨Nat.mem_antidiagonalTuple.mpr (by simpa [join, Fin.sum_cons, hs] using hp),
            Fin.cases ha hv⟩
      · intro c _
        exact Fin.cons_self_tail c
      · rintro ⟨p, c⟩ hz
        obtain ⟨_, _, hs, _⟩ := (mem_pieces _ _).mp hz
        simp [split, join, hs]
    _ = _ := by simp [pieces, card_sigma, sum_filter]

private lemma count_eq_sum (j : ℕ) {n N : ℕ} (h : n ≤ N) :
    oddOrSmallEvenCompositionCount j n = ∑ m ∈ range (N + 1), (tuples j m n).card := by
  apply sum_subset (range_mono (by omega))
  intro m _ hm
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨hs, hv⟩ := mem_filter.mp hc
  have hlength := sum_le_sum (s := univ) fun i _ => (show 1 ≤ c i from (hv i).1)
  simp [Nat.mem_antidiagonalTuple.mp hs] at hlength
  simp only [mem_range] at hm
  omega

private lemma count_split (j n : ℕ) :
    oddOrSmallEvenCompositionCount j n = (if n = 0 then 1 else 0) +
      ∑ p ∈ antidiagonal n, if allowed j p.1 then oddOrSmallEvenCompositionCount j p.2 else 0 := by
  have hzero : (tuples j 0 n).card = if n = 0 then 1 else 0 := by
    cases n <;> simp [tuples]
  rw [count_eq_sum j (N := n + 1) (by omega), sum_range_succ', hzero, add_comm]
  congr 1
  simp_rw [tuples_succ]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  by_cases ha : allowed j p.1
  · simp only [ite_eq_left ha]
    have hp' : p.2 ≤ n := by have := mem_antidiagonal.mp hp; omega
    exact (count_eq_sum j hp').symm
  · simp [ha]

private noncomputable def countSeries (j : ℕ) : PowerSeries ℤ :=
  mk fun n => (oddOrSmallEvenCompositionCount j n : ℤ)

private noncomputable def partSeries (j : ℕ) : PowerSeries ℤ :=
  mk fun n => if allowed j n then 1 else 0

private lemma series_split (j : ℕ) : countSeries j = 1 + partSeries j * countSeries j := by
  apply PowerSeries.ext
  intro n
  simpa [countSeries, partSeries, coeff_one, coeff_mul, apply_ite, ite_mul] using
    congrArg (fun a : ℕ => (a : ℤ)) (count_split j n)

-- Shifting the allowed parts by two cancels all terms except at 1, 2, and 2j + 2.
private lemma part_mul (j : ℕ) (hj : 1 ≤ j) :
    partSeries j * (1 - X ^ 2) = X + X ^ 2 - X ^ (2 * j + 2) := by
  apply PowerSeries.ext
  intro n
  simp only [mul_sub, mul_one, map_sub, map_add, coeff_X, coeff_X_pow, coeff_mul_X_pow',
    partSeries, coeff_mk, allowed, Nat.odd_iff]
  split_ifs <;> omega

private lemma count_mul (j : ℕ) (hj : 1 ≤ j) :
    countSeries j - countSeries j * X ^ 1 - 2 * (countSeries j * X ^ 2) +
        countSeries j * X ^ (2 * j + 2) = 1 - X ^ 2 := by
  calc
    _ = (countSeries j - partSeries j * countSeries j) * (1 - X ^ 2) := by
      rw [sub_mul, mul_right_comm (partSeries j), part_mul j hj]
      ring
    _ = _ := by
      rw [sub_eq_iff_eq_add.mpr (series_split j), one_mul]

private lemma count_recurrence (j n : ℕ) (hj : 1 ≤ j) (hn : 3 ≤ n) :
    (oddOrSmallEvenCompositionCount j n : ℤ) =
      oddOrSmallEvenCompositionCount j (n - 1) + 2 * oddOrSmallEvenCompositionCount j (n - 2) -
        if 2 * j + 2 ≤ n then (oddOrSmallEvenCompositionCount j (n - 2 - 2 * j) : ℤ) else 0 := by
  have h := congrArg (coeff (R := ℤ) n) (count_mul j hj)
  rw [show (2 : PowerSeries ℤ) = C 2 by simp] at h
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_C_mul, countSeries, coeff_mk,
    coeff_one, coeff_X_pow, ite_eq_right (show n ≠ 0 by omega),
    ite_eq_right (show n ≠ 2 by omega), sub_zero, ite_eq_left (show 1 ≤ n by omega),
    ite_eq_left (show 2 ≤ n by omega)] at h
  rw [Nat.sub_sub, Nat.add_comm 2]
  omega

end kArndtTotalCount_neg_even

open kArndtTotalCount_neg_even in
/-- **Generalized Arndt compositions with negative even shift.** For every natural number
$j \ge 1$ and every natural number $n$, the number $a(n, -2j)$ of compositions
$(c_1, \dots, c_m)$ of $n$ with $c_{2i-1} > c_{2i} - 2j$ whenever $2i \le m$ equals the number
$c^{2j}_o(n)$ of compositions of $n$ in which every part is odd or at most $2j$. This includes
$n = 0$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 5 (`integers-2026-A64-thm-5`). -/
public theorem kArndtTotalCount_neg_even (j n : ℕ) (hj : 1 ≤ j) :
    kArndtTotalCount (-(2 * j : ℤ)) n = oddOrSmallEvenCompositionCount j n := by
  have hshift : (-(2 * j : ℤ)) = -((2 * j : ℕ) : ℤ) := by push_cast; rfl
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : 3 ≤ n
    · have harndt := kArndtTotalCount_recurrence.1 (2 * j) n hn
      rw [← hshift, ih (n - 1) (by omega), ih (n - 2) (by omega),
        ih (n - 2 - 2 * j) (by omega)] at harndt
      exact_mod_cast harndt.trans (count_recurrence j n hj hn).symm
    · obtain rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      all_goals
        simp [kArndtTotalCount, kArndtCompositionCount, oddOrSmallEvenCompositionCount,
          Finset.sum_range_succ, Fin.forall_fin_one, Finset.filter_singleton, Nat.odd_iff, hj]
      -- At weight two, only (1, 1) has two positive parts.
      have hpairs : Finset.Nat.antidiagonalTuple 2 2 = {![0, 2], ![1, 1], ![2, 0]} := by
        decide
      simp [hpairs, Finset.filter_insert, Finset.filter_singleton,
        show (1 : ℤ) < 1 + 2 * (j : ℤ) by omega]

end MetaMathlibExt
