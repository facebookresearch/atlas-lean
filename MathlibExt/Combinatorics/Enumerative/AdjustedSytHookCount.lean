/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MotzkinHumpsYoungTableaux
import all MathlibExt.Combinatorics.Enumerative.MotzkinHumpsYoungTableaux
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring

/-!
# Generating function for adjusted hook tableau counts

For fixed first-two-row difference, multiplying the adjusted tableau series by `1 + X`
gives the corresponding power of the shifted Motzkin series.
-/

namespace MetaMathlibExt

namespace adjustedSytHookCount_generatingFunction

open PowerSeries sytHookCount_add_eq_humpCount_sub

private noncomputable abbrev shiftedMotzkin : PowerSeries ℤ := X * motzkinSeries

-- The Motzkin recurrence in power series form.
private theorem series_eq : motzkinSeries = 1 + shiftedMotzkin + shiftedMotzkin ^ 2 := by
  rw [show shiftedMotzkin ^ 2 = X * (X * (motzkinSeries * motzkinSeries)) by
    unfold shiftedMotzkin
    ring]
  ext n
  rcases n with _ | n
  · simp [shiftedMotzkin, motzkinSeries, coeff_zero_eq_constantCoeff_apply, motzkinNumber_zero]
  rcases n with _ | n
  · simp [shiftedMotzkin, coeff_succ_X_mul, motzkinSeries, motzkinNumber_zero, motzkinNumber_one,
      coeff_zero_X_mul, coeff_one]
  simp only [map_add, coeff_one, Nat.succ_ne_zero, ite_false, zero_add, shiftedMotzkin,
    coeff_succ_X_mul, motzkinSeries, coeff_mk]
  rw [coeff_mul]
  simp only [coeff_mk]
  rw [motzkinNumber_succ (n + 1), Nat.cast_add, Nat.cast_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => (motzkinNumber a : ℤ) * motzkinNumber b), Finset.sum_range]
  simp

-- The three terms correspond to the three possible last steps of a Motzkin prefix.
private theorem power_step (k : ℕ) :
    shiftedMotzkin ^ (k + 1) =
      X * (shiftedMotzkin ^ k + shiftedMotzkin ^ (k + 1) + shiftedMotzkin ^ (k + 2)) := by
  calc
    shiftedMotzkin ^ (k + 1) = shiftedMotzkin ^ k * (X * motzkinSeries) := pow_succ _ _
    _ = shiftedMotzkin ^ k * (X * (1 + shiftedMotzkin + shiftedMotzkin ^ 2)) := by rw [← series_eq]
    _ = _ := by ring

private theorem coeff_power (n k : ℕ) :
    coeff (n + 1) (shiftedMotzkin ^ (k + 1)) = (walkCount n 0 k : ℤ) := by
  induction n generalizing k with
  | zero =>
    rw [power_step, coeff_succ_X_mul]
    cases k <;> simp [shiftedMotzkin, coeff_zero_eq_constantCoeff_apply, walkCount]
  | succ n ih =>
    rw [power_step, coeff_succ_X_mul, map_add, map_add]
    cases k with
    | zero =>
      rw [ih 0, ih 1, pow_zero, coeff_one, ite_eq_right (Nat.succ_ne_zero _), zero_add,
        walkCount, Nat.cast_add]
    | succ k =>
      simp only [ih, walkCount, Nat.cast_add]

private theorem count_eq_zero {n k : ℕ} (h : n < k) : sytHookCount n k = 0 := by
  unfold sytHookCount
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun ⟨T, _, _, hd⟩ => ?_⟩
  have hrow : tableauRowLength n T 0 ≤ n := by
    simpa [tableauRowLength] using
      (Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => (T i).1.val = 0))
  unfold HasFirstTwoRowDifference at hd
  omega

private def correction (n k : ℕ) : ℤ :=
  if k ≤ n then (-1 : ℤ) ^ (n + k + 1) else 0

private theorem adjusted_eq (n k : ℕ) :
    (if k ≤ n then (sytHookCount n k : ℤ) + (-1 : ℤ) ^ (n + k + 1) else 0) =
      sytHookCount n k + correction n k := by
  by_cases h : k ≤ n
  · simp [correction, h]
  · simp [correction, h, count_eq_zero (Nat.lt_of_not_ge h)]

private theorem correction_add (n k : ℕ) :
    correction (n + 1) k + correction n k = - (if n + 1 = k then 1 else 0) := by
  obtain h | rfl | h := lt_trichotomy (n + 1) k
  · simp [correction, Nat.not_le_of_gt h, show ¬k ≤ n by omega, h.ne]
  · simp [correction, pow_succ, pow_add, ← mul_pow]
  · simp [correction, h.le, show k ≤ n by omega, h.ne',
      show n + 1 + k + 1 = (n + k + 1) + 1 by omega, pow_succ]

end adjustedSytHookCount_generatingFunction

open adjustedSytHookCount_generatingFunction
open sytHookCount_add_eq_humpCount_sub

/-- **Generating function for the adjusted $(2,1)$-hook tableau counts.** Let $k$ be a natural
number, and let $\mathrm{SYT}_k(2,1;n)$ be the number of standard Young tableaux with $n$ cells
in the $(2,1)$-hook whose first two rows differ in length by $k$. Set
$T_{n,k} = \mathrm{SYT}_k(2,1;n) + (-1)^{n+k+1}$ for $n \ge k$ and $T_{n,k} = 0$ for $n < k$, and
let $M(x) = \sum_{n \ge 0} m_n x^n$ be the generating function of the Motzkin numbers $m_n$.
Then in the ring $\mathbb{Z}[[x]]$ of formal power series

$$(1 + x) \sum_{n \ge 0} T_{n,k} x^n = (x M(x))^{k+1}.$$

Equivalently, $\sum_{n \ge k} T_{n,k} x^n = x^{k+1} M(x)^{k+1} / (1 + x)$; the identity is
stated without division.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 7 (`jis-2025-25.8.1-lem-7`).
-/
public theorem adjustedSytHookCount_generatingFunction (k : ℕ) :
    (1 + (PowerSeries.X : PowerSeries ℤ)) *
        PowerSeries.mk (fun n =>
          if k ≤ n then (sytHookCount n k : ℤ) + (-1 : ℤ) ^ (n + k + 1) else 0) =
      (PowerSeries.X * motzkinSeries) ^ (k + 1) := by
  ext n
  rw [add_mul, one_mul, map_add]
  cases n with
  | zero =>
    cases k <;>
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, syt_eq_fromRow, fromRow, pow_succ]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      adjusted_eq, adjusted_eq, coeff_power]
    have h := fromRow_add n 0 k
    simp only [← syt_eq_fromRow, lt_irrefl, ite_false, add_zero, zero_add] at h
    have hc := correction_add n k
    split_ifs at h hc <;> omega

end MetaMathlibExt
