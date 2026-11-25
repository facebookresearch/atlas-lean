/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MotzkinHumpsYoungTableaux
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring

/-!
# Generating function for humps of a fixed height

For each positive height `k`, `motzkinHumpCount_generatingFunction` identifies the series of
marked humps multiplied by `1 - X` with `X ^ (2 * k) * motzkinSeries ^ (2 * k)`.
-/

namespace MetaMathlibExt

open PowerSeries sytHookCount_add_eq_humpCount_sub

namespace motzkinHumpCount_generatingFunction

private theorem motzkin_equation :
    motzkinSeries = 1 + X * (motzkinSeries + X * (motzkinSeries * motzkinSeries)) := by
  ext n
  cases n with
  | zero => simp [motzkinSeries, motzkinNumber_zero]
  | succ n =>
    simp only [map_add, coeff_one, Nat.succ_ne_zero, ite_false, zero_add, coeff_succ_X_mul]
    cases n with
    | zero => simp [motzkinSeries, motzkinNumber_zero, motzkinNumber_one]
    | succ n =>
      rw [coeff_succ_X_mul, coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => coeff i motzkinSeries * coeff j motzkinSeries),
        Finset.sum_range]
      simp only [motzkinSeries, coeff_mk]
      exact_mod_cast motzkinNumber_succ (n + 1)

-- The column indexed by h counts walks from height zero to height h.
private noncomputable def column (h : ℕ) : PowerSeries ℤ :=
  motzkinSeries * (X * motzkinSeries) ^ h

private theorem column_zero : column 0 = 1 + X * (column 0 + column 1) := by
  simpa [column, mul_left_comm] using motzkin_equation

private theorem column_succ (h : ℕ) :
    column (h + 1) = X * (column h + column (h + 1) + column (h + 2)) := by
  unfold column
  calc
    _ = X * (motzkinSeries * (X * motzkinSeries) ^ h) * motzkinSeries := by ring
    _ = _ := by
      conv_lhs => rhs; rw [motzkin_equation]
      ring

private theorem coeff_column (n h : ℕ) : coeff n (column h) = (walkCount n 0 h : ℤ) := by
  induction n generalizing h with
  | zero =>
    cases h <;> simp [column, motzkinSeries, motzkinNumber_zero, walkCount]
  | succ n ih =>
    cases h with
    | zero =>
      rw [column_zero, map_add, coeff_one, ite_eq_right (by omega), zero_add, coeff_succ_X_mul,
        map_add, ih, ih, walkCount, Nat.cast_add]
    | succ h =>
      rw [column_succ, coeff_succ_X_mul, map_add, map_add, ih, ih, ih, walkCount]
      push_cast
      rfl

private theorem humpCount_small {n : ℕ} (hn : n ≤ 1) (k : ℕ) : motzkinHumpCount n k = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  constructor
  rintro ⟨⟨_, i, j⟩, _, hump⟩
  have := hump.1
  omega

private theorem humpCount_two_of_one_lt {k : ℕ} (hk : 1 < k) : motzkinHumpCount 2 k = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  constructor
  rintro ⟨⟨p, i, j⟩, _, hij, hup, _, _, height⟩
  dsimp only at hij hup height
  have hi : i = 0 := Fin.ext (by change i.val = 0; omega)
  subst i
  simp [hup] at height
  omega

-- Extend the walk recurrence to the empty path and the first possible hump.
private theorem humpCount_step (n k : ℕ) (hk : 1 ≤ k) :
    motzkinHumpCount (n + 1) k = motzkinHumpCount n k + walkCount n 0 (2 * k - 1) := by
  obtain _ | _ | n := n
  · simp [humpCount_small (n := 1) (by decide), humpCount_small (n := 0) (by decide),
      walkCount, show 0 ≠ 2 * k - 1 by omega]
  · rw [humpCount_small (n := 1) (by decide), zero_add]
    obtain rfl | h := eq_or_lt_of_le hk
    · decide
    · rw [humpCount_two_of_one_lt h]
      have hb : 2 * k - 1 = (2 * k - 3) + 2 := by omega
      simp [hb, walkCount]
  · exact humpCount_succ _ k (by omega) hk

private theorem coeff_hump_step (n k : ℕ) (hk : 1 ≤ k) :
    coeff (n + 1) (X ^ (2 * k) * motzkinSeries ^ (2 * k)) =
      (motzkinHumpCount (n + 1) k : ℤ) - motzkinHumpCount n k := by
  have he : 2 * k = (2 * k - 1) + 1 := by omega
  conv_lhs =>
    rw [← mul_pow, he, pow_succ, mul_comm, mul_assoc, ← column, coeff_succ_X_mul]
  rw [coeff_column, humpCount_step n k hk, Nat.cast_add]
  abel

private theorem humpCount_below {n k : ℕ} (hk : 1 ≤ k) (hn : n < 2 * k) :
    motzkinHumpCount n k = 0 := by
  induction n with
  | zero => exact humpCount_small (by decide) _
  | succ n ih =>
    have h := coeff_hump_step n k hk
    rw [coeff_X_pow_mul', ite_eq_right (by omega), ih (by omega), Nat.cast_zero, sub_zero] at h
    exact_mod_cast h.symm

end motzkinHumpCount_generatingFunction

open motzkinHumpCount_generatingFunction

/-- **Generating function for humps of a fixed height.** Let $H_{n,k}$ be the number of pairs
$(P, h)$ where $P$ is a Motzkin path of length $n$ and $h$ is a hump of height $k$ in $P$ (an up
step and a later down step with only flat steps between them, the up step ending at height
$k$), and let $M(x) = \sum_{n \ge 0} m_n x^n$, where $m_n$ is the $n$-th Motzkin number. For
every integer $k \ge 1$, in the ring $\mathbb{Z}[[x]]$ of formal power series,
$$(1 - x) \sum_{n \ge 2k} H_{n,k} \, x^n = x^{2k} M(x)^{2k}.$$

The source also states this result in Riordan-array form.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Corollary 5 (`jis-2025-25.8.1-cor-5`).
-/
public theorem motzkinHumpCount_generatingFunction (k : ℕ) (hk : 1 ≤ k) :
    (1 - (PowerSeries.X : PowerSeries ℤ)) *
        PowerSeries.mk (fun n => if 2 * k ≤ n then (motzkinHumpCount n k : ℤ) else 0) =
      PowerSeries.X ^ (2 * k) * motzkinSeries ^ (2 * k) := by
  have cutoff (n : ℕ) :
      (if 2 * k ≤ n then (motzkinHumpCount n k : ℤ) else 0) = motzkinHumpCount n k := by
    split
    · rfl
    · rw [humpCount_below hk (by omega), Nat.cast_zero]
  simp_rw [cutoff]
  rw [sub_mul, one_mul]
  ext n
  cases n with
  | zero =>
    simp [motzkinSeries, humpCount_small (n := 0) (by decide), show 2 * k ≠ 0 by omega]
  | succ n =>
    simpa only [map_sub, coeff_mk, coeff_succ_X_mul] using (coeff_hump_step n k hk).symm

end MetaMathlibExt
