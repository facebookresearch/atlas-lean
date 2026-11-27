/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.NExpansionGaps
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.NormNum.Basic

/-! # Tests for `MathlibExt.Dynamics.NExpansionGaps` -/

namespace MathlibExtTest.Dynamics.NExpansionGaps

open MetaMathlibExt

-- Test section: the digit and the map for `N = 2` and `α = 1`. Here `N/α - α = 1` is an integer,
-- so the digit of `α = 1` is lowered from `⌊1⌋ = 1` to `0` and `T_1(1) = 2 = α + 1`; then
-- `T_1(2) = 1`, so the orbit of `1` is `1, 2, 1, 2, ...`, with digits `0`.
private theorem nExpansionMap_two_one_one : nExpansionMap 2 1 1 = 2 := by
  rw [nExpansionMap_self_of_int (k := 1) (by norm_num)]
  norm_num

private theorem nExpansionDigit_two_one_one : nExpansionDigit 2 1 1 = 0 := by
  have h := nExpansionMap_two_one_one
  rw [nExpansionMap] at h
  have h' : (nExpansionDigit 2 1 1 : ℝ) = 0 := by
    have h₂ : ((2 : ℕ) : ℝ) / 1 = 2 := by norm_num
    linarith
  exact_mod_cast h'

example : nExpansionDigit 2 1 1 = ⌊(2 : ℝ) / 1 - 1⌋ - 1 := by
  rw [nExpansionDigit_two_one_one]
  norm_num

private theorem nExpansionDigit_two_one_two : nExpansionDigit 2 1 2 = 0 := by
  rw [nExpansionDigit_of_ne (by norm_num), Int.floor_eq_iff]
  norm_num

private theorem nExpansionMap_two_one_two : nExpansionMap 2 1 2 = 1 := by
  rw [nExpansionMap, nExpansionDigit_two_one_two]
  norm_num

example : (nExpansionMap 2 1)^[2] 1 = 1 := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, nExpansionMap_two_one_one,
    nExpansionMap_two_one_two]

-- Test section: for `N = 2` and `α' = 11/10`, `N/α' - α' = 79/110` is not an integer, so the
-- digit of `α'` is `⌊79/110⌋ = 0`. The orbit of `11/10` is `11/10, 20/11, 11/10, ...`, with digits
-- `0`, the same as the digits of the orbit of `1` for `α = 1`.
private theorem nExpansionDigit_two_eleven_tenths_self :
    nExpansionDigit 2 (11 / 10) (11 / 10) = 0 := by
  have hk : ¬ ∃ k : ℤ, ((2 : ℕ) : ℝ) / (11 / 10) - 11 / 10 = k := by
    rintro ⟨k, hk⟩
    have h₀ : (0 : ℝ) < k := by
      rw [← hk]
      norm_num
    have h₁ : (k : ℝ) < 1 := by
      rw [← hk]
      norm_num
    have h₀' : 0 < k := by exact_mod_cast h₀
    have h₁' : k < 1 := by exact_mod_cast h₁
    omega
  rw [nExpansionDigit, ite_eq_right fun h => hk h.2, Int.floor_eq_iff]
  norm_num

private theorem nExpansionDigit_two_eleven_tenths_twenty_elevenths :
    nExpansionDigit 2 (11 / 10) (20 / 11) = 0 := by
  rw [nExpansionDigit_of_ne (by norm_num), Int.floor_eq_iff]
  norm_num

private theorem nExpansionMap_two_eleven_tenths_self :
    nExpansionMap 2 (11 / 10) (11 / 10) = 20 / 11 := by
  rw [nExpansionMap, nExpansionDigit_two_eleven_tenths_self]
  norm_num

private theorem nExpansionMap_two_eleven_tenths_twenty_elevenths :
    nExpansionMap 2 (11 / 10) (20 / 11) = 11 / 10 := by
  rw [nExpansionMap, nExpansionDigit_two_eleven_tenths_twenty_elevenths]
  norm_num

/-- The orbits of `1` for `α = 1` and of `11/10` for `α' = 11/10` (with `N = 2`) have the same
digits at the steps `0, 1, 2`, so the hypothesis of the alternation theorem holds for `m = 2`. -/
private theorem digits_agree_two :
    ∀ j ≤ 2, nExpansionDigit 2 1 ((nExpansionMap 2 1)^[j] 1) =
      nExpansionDigit 2 (11 / 10) ((nExpansionMap 2 (11 / 10))^[j] (11 / 10)) := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;>
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      nExpansionMap_two_one_one, nExpansionMap_two_one_two, nExpansionMap_two_eleven_tenths_self,
      nExpansionMap_two_eleven_tenths_twenty_elevenths, nExpansionDigit_two_one_one,
      nExpansionDigit_two_one_two, nExpansionDigit_two_eleven_tenths_self,
      nExpansionDigit_two_eleven_tenths_twenty_elevenths]

-- Test section: the alternation theorem on these orbits. At the odd step `1` the orbit of the
-- larger parameter is below (`20/11 < 2`); at the even step `2` it is not (`11/10 ≥ 1`), and the
-- direct computation agrees.
example : (nExpansionMap 2 (11 / 10))^[1] (11 / 10) < (nExpansionMap 2 1)^[1] 1 :=
  ((nExpansion_orbit_gt_iff_odd (by norm_num) (by norm_num) (by norm_num) 1).1
    fun j hj => digits_agree_two j (by omega)).2 odd_one

example : ¬ (nExpansionMap 2 (11 / 10))^[2] (11 / 10) < (nExpansionMap 2 1)^[2] 1 := by
  rw [((nExpansion_orbit_gt_iff_odd (by norm_num) (by norm_num) (by norm_num) 2).1
    digits_agree_two)]
  decide

example : (nExpansionMap 2 (11 / 10))^[2] (11 / 10) = 11 / 10 ∧ (nExpansionMap 2 1)^[2] 1 = 1 := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, nExpansionMap_two_one_one,
    nExpansionMap_two_one_two, nExpansionMap_two_eleven_tenths_self,
    nExpansionMap_two_eleven_tenths_twenty_elevenths, and_self]

-- Test section: for even `m` the theorem gives the weak inequality `α_m ≤ α'_m` between the
-- points of index `m`.
example {N : ℕ} (hN : 0 < N) {α α' : ℝ} (hα : 0 < α) (hαα' : α < α') {m : ℕ} (hm : Even m)
    (hd : ∀ j ≤ m, nExpansionDigit N α ((nExpansionMap N α)^[j] α) =
      nExpansionDigit N α' ((nExpansionMap N α')^[j] α')) :
    (nExpansionMap N α)^[m] α ≤ (nExpansionMap N α')^[m] α' :=
  not_lt.mp fun h =>
    Nat.not_odd_iff_even.mpr hm (((nExpansion_orbit_gt_iff_odd hN hα hαα' m).1 hd).mp h)

-- Test section: the hypothesis `0 < N` is needed. For `N = 0` and `0 < α < 1` every digit is
-- `⌊-α⌋ = -1` (also at `α`, since `-α` is not an integer), so `T_α` is constant equal to `1`. For
-- `α = 1/5` and `α' = 3/10` the orbits have the same digits `-1, -1`, but their points of index
-- `1` are equal although `1` is odd.
private theorem nExpansionDigit_zero {α : ℝ} (h₀ : 0 < α) (h₁ : α < 1) (x : ℝ) :
    nExpansionDigit 0 α x = -1 := by
  have hk : ¬ ∃ k : ℤ, ((0 : ℕ) : ℝ) / α - α = k := by
    rintro ⟨k, hk⟩
    have hk₀ : (k : ℝ) < 0 := by
      rw [← hk]
      simp [h₀]
    have hk₁ : (-1 : ℝ) < k := by
      rw [← hk]
      simp only [Nat.cast_zero, zero_div, zero_sub, neg_lt_neg_iff, h₁]
    have hk₀' : k < 0 := by exact_mod_cast hk₀
    have hk₁' : -1 < k := by exact_mod_cast hk₁
    omega
  rw [nExpansionDigit, ite_eq_right fun h => hk h.2, Int.floor_eq_iff]
  constructor <;> simp <;> linarith

private theorem nExpansionMap_zero {α : ℝ} (h₀ : 0 < α) (h₁ : α < 1) (x : ℝ) :
    nExpansionMap 0 α x = 1 := by
  rw [nExpansionMap, nExpansionDigit_zero h₀ h₁]
  simp

example : ¬ ((∀ j ≤ 1, nExpansionDigit 0 (1 / 5) ((nExpansionMap 0 (1 / 5))^[j] (1 / 5)) =
      nExpansionDigit 0 (3 / 10) ((nExpansionMap 0 (3 / 10))^[j] (3 / 10))) →
    ((nExpansionMap 0 (3 / 10))^[1] (3 / 10) < (nExpansionMap 0 (1 / 5))^[1] (1 / 5) ↔
      Odd 1)) := by
  intro h
  have hd : ∀ j ≤ 1, nExpansionDigit 0 (1 / 5) ((nExpansionMap 0 (1 / 5))^[j] (1 / 5)) =
      nExpansionDigit 0 (3 / 10) ((nExpansionMap 0 (3 / 10))^[j] (3 / 10)) := fun j _ => by
    rw [nExpansionDigit_zero (by norm_num) (by norm_num),
      nExpansionDigit_zero (by norm_num) (by norm_num)]
  have h₁ := (h hd).mpr odd_one
  rw [Function.iterate_one, Function.iterate_one, nExpansionMap_zero (by norm_num) (by norm_num),
    nExpansionMap_zero (by norm_num) (by norm_num)] at h₁
  exact lt_irrefl _ h₁

-- Test section: the two recursion rules alternate. `d_4 = [j, abb]`, so `d_5` comes from the
-- second rule and ends with `ab, ab`; then `d_6` comes from the first rule and ends with `abb`.
example : (idealPeriodWord 5).drop ((idealPeriodWord 5).length - 4) =
    [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] := by
  decide

example : (idealPeriodWord 6).drop ((idealPeriodWord 6).length - 3) =
    [[2, 1, 1], [2, 2], [2, 2]] := by
  decide

-- The formula starts at the first word. At index zero the placeholder word is empty.
example : (idealPeriodWord 1).flatten.length = 5 := by
  have h := idealPeriodWord_flatten_length (n := 1) (by decide)
  norm_num at h
  exact_mod_cast h

example : ((idealPeriodWord 0).flatten.length : ℤ) ≠ 2 ^ (0 + 1 : ℕ) - (-1) ^ (0 : ℕ) := by
  decide

-- Across two consecutive indices the parity corrections cancel.
example {n : ℕ} (hn : 1 ≤ n) :
    ((idealPeriodWord n).flatten.length : ℤ) + (idealPeriodWord (n + 1)).flatten.length =
      3 * 2 ^ (n + 1) := by
  rw [idealPeriodWord_flatten_length hn, idealPeriodWord_flatten_length (by omega)]
  ring

-- Test section: block counts computed directly from the recursion, beyond the explicit words.
-- `d_6` has `2^5 = 32` blocks `2, 2` and `(2^6 - 1)/3 = 21` blocks `2, 1, 1`; `d_7` has `64` and
-- `(2^7 + 1)/3 = 43`.
example : (idealPeriodWord 6).count [2, 2] = 32 ∧ (idealPeriodWord 6).count [2, 1, 1] = 21 := by
  decide

set_option maxRecDepth 4000 in
example : (idealPeriodWord 7).count [2, 2] = 64 ∧ (idealPeriodWord 7).count [2, 1, 1] = 43 := by
  decide

-- Test section: Lemma 8 at `n = 10`, where `d_10` has `2^9 = 512` blocks `2, 2` and
-- `(2^10 - 1)/3 = 341` blocks `2, 1, 1`.
example : (idealPeriodWord 10).count [2, 2] = 512 ∧ (idealPeriodWord 10).count [2, 1, 1] = 341 := by
  obtain ⟨hb, ha⟩ := idealPeriodWord_count_blocks (n := 10) (by norm_num)
  refine ⟨hb, ?_⟩
  norm_num at ha
  omega

-- Test section: the two parity forms of the count `c_n` of blocks `2, 1, 1`:
-- `3 c_n = 2^n + 1` for odd `n` and `3 c_n = 2^n - 1` for even `n ≥ 2`.
example {n : ℕ} (hn : Odd n) : 3 * ((idealPeriodWord n).count [2, 1, 1] : ℤ) = 2 ^ n + 1 := by
  have h₁ : 1 ≤ n := by
    obtain ⟨k, rfl⟩ := hn
    omega
  rw [(idealPeriodWord_count_blocks h₁).2, hn.neg_one_pow, sub_neg_eq_add]

example {n : ℕ} (hn : Even n) (hn₂ : 2 ≤ n) :
    3 * ((idealPeriodWord n).count [2, 1, 1] : ℤ) = 2 ^ n - 1 := by
  rw [(idealPeriodWord_count_blocks (by omega)).2, hn.neg_one_pow]

-- Test section: the number of blocks `2, 2` doubles from each word to the next.
example {n : ℕ} (hn : 1 ≤ n) :
    (idealPeriodWord (n + 1)).count [2, 2] = 2 * (idealPeriodWord n).count [2, 2] := by
  rw [(idealPeriodWord_count_blocks (by omega)).1, (idealPeriodWord_count_blocks hn).1,
    ← pow_succ']
  congr 1
  omega

-- Test section: the hypothesis `1 ≤ n` is needed. The placeholder `d_0` is empty, so it has no
-- block `2, 2`, while `2^(0 - 1) = 1` in `ℕ`.
example : ¬ (idealPeriodWord 0).count [2, 2] = 2 ^ (0 - 1) := by
  decide

end MathlibExtTest.Dynamics.NExpansionGaps
