/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Exponential lower bound for the absolute discriminant

This file proves the second inequality of ATLAS `NumberTheoryI`
Corollary 14.26: for a number field `K` of degree `n` with `s` complex
places,
$$|D_K| \ge \left(\frac{n^n}{n!}\right)^2 \left(\frac{\pi}{4}\right)^{2s}
  > \frac{1}{e^2 n} \left(\frac{\pi e^2}{4}\right)^n.$$

The first inequality is Mathlib's `NumberField.abs_discr_ge'`; the second,
which says the discriminant grows at least exponentially in the degree,
is new here. Its proof is a sharp Stirling bound: the Stirling sequence
`n! / (√(2n) (n / e) ^ n)` is antitone, hence at most its value `e / √2`
at `n = 1`, so `n! ≤ √n * n ^ n / e ^ (n - 1)`, with strict inequality
for `n ≥ 2` (the `n = 2` case is the numeric bound `e ^ 2 < 8`).
-/

@[expose] public section

namespace NumberField

open NumberField.InfinitePlace

/-- The Stirling sequence at `2` is strictly less than at `1`, by the
numeric bound `e ^ 2 < 8`. -/
private theorem stirlingSeq_two_lt_one :
    Stirling.stirlingSeq 2 < Stirling.stirlingSeq 1 := by
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he2 : Real.exp 1 ^ 2 < 8 := by
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hsqrt4 : Real.sqrt (2 * ((2 : ℕ) : ℝ)) = 2 := by
    rw [show (2 * ((2 : ℕ) : ℝ)) = (2 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hsqrt2_lt : Real.sqrt 2 < 1.42 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1.42)]; norm_num
  have he_sqrt : Real.exp 1 * Real.sqrt 2 < 4 := by
    calc Real.exp 1 * Real.sqrt 2
        < 2.7182818286 * 1.42 := by
          apply mul_lt_mul Real.exp_one_lt_d9 (le_of_lt hsqrt2_lt)
            (by positivity) (by norm_num)
      _ < 4 := by norm_num
  rw [Stirling.stirlingSeq, Stirling.stirlingSeq_one, hsqrt4]
  have hfact : (Nat.factorial 2 : ℝ) = 2 := by norm_num
  rw [hfact]
  rw [div_pow, show ((2 : ℕ) : ℝ) ^ 2 = (4 : ℝ) by norm_num]
  rw [show (2 : ℝ) * (4 / Real.exp 1 ^ 2) = 8 / Real.exp 1 ^ 2 by
    field_simp; ring]
  have hLHS : 2 / (8 / Real.exp 1 ^ 2) = Real.exp 1 ^ 2 / 4 := by
    field_simp; ring
  rw [hLHS]
  calc Real.exp 1 ^ 2 / 4
      = (Real.exp 1 * Real.sqrt 2) *
          (Real.exp 1 / (4 * Real.sqrt 2)) := by
        field_simp
    _ < 4 * (Real.exp 1 / (4 * Real.sqrt 2)) := by
        apply mul_lt_mul_of_pos_right he_sqrt (by positivity)
    _ = Real.exp 1 / Real.sqrt 2 := by field_simp

/-- Stirling-sequence bound, non-strict:
`n! ≤ √n * n ^ n / e ^ (n - 1)`. -/
private theorem factorial_le_sqrt_mul_pow_div_exp (n : ℕ) (hn : n ≠ 0) :
    (Nat.factorial n : ℝ) ≤
      Real.sqrt n * (n : ℝ) ^ n / Real.exp 1 ^ (n - 1) := by
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hanti : Stirling.stirlingSeq (m + 1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  rw [Stirling.stirlingSeq_one] at hanti
  have hpos : (0 : ℝ) < Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) *
      (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1) := by
    positivity
  have hfact : (Nat.factorial (m + 1) : ℝ) =
      Stirling.stirlingSeq (m + 1) *
        (Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) *
          (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1)) := by
    rw [Stirling.stirlingSeq]; field_simp
  rw [hfact]
  have hsqrt : Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) =
      Real.sqrt 2 * Real.sqrt ((m + 1 : ℕ) : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have he : Real.exp 1 ^ (m + 1) = Real.exp 1 ^ m * Real.exp 1 := by
    rw [pow_succ]
  have h2 : ((m + 1 : ℕ) : ℝ) / Real.exp 1 =
      ((m + 1 : ℕ) : ℝ) * (Real.exp 1)⁻¹ := by ring
  rw [hsqrt]
  rw [div_pow]
  have hsqrt2 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hexp : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
  calc Stirling.stirlingSeq (m + 1) *
        (Real.sqrt 2 * Real.sqrt ((m + 1 : ℕ) : ℝ) *
          (((m + 1 : ℕ) : ℝ) ^ (m + 1) / Real.exp 1 ^ (m + 1)))
      ≤ (Real.exp 1 / Real.sqrt 2) *
          (Real.sqrt 2 * Real.sqrt ((m + 1 : ℕ) : ℝ) *
            (((m + 1 : ℕ) : ℝ) ^ (m + 1) / Real.exp 1 ^ (m + 1))) := by
        apply mul_le_mul_of_nonneg_right hanti (by positivity)
    _ = Real.sqrt ((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) ^ (m + 1) /
        Real.exp 1 ^ m := by
        rw [he]; field_simp

/-- Stirling-sequence bound, strict for `n ≥ 2`:
`n! < √n * n ^ n / e ^ (n - 1)`. -/
private theorem factorial_lt_sqrt_mul_pow_div_exp (n : ℕ) (hn : 2 ≤ n) :
    (Nat.factorial n : ℝ) <
      Real.sqrt n * (n : ℝ) ^ n / Real.exp 1 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hanti : Stirling.stirlingSeq (m + 2) ≤ Stirling.stirlingSeq 2 :=
    Stirling.stirlingSeq'_antitone
      (Nat.one_le_iff_ne_zero.mpr (by omega : m + 1 ≠ 0))
  have hlt : Stirling.stirlingSeq (m + 2) < Stirling.stirlingSeq 1 :=
    lt_of_le_of_lt hanti stirlingSeq_two_lt_one
  rw [Stirling.stirlingSeq_one] at hlt
  have hfact : (Nat.factorial (m + 2) : ℝ) =
      Stirling.stirlingSeq (m + 2) *
        (Real.sqrt (2 * ((m + 2 : ℕ) : ℝ)) *
          (((m + 2 : ℕ) : ℝ) / Real.exp 1) ^ (m + 2)) := by
    rw [Stirling.stirlingSeq]; field_simp
  rw [hfact]
  have hsqrt : Real.sqrt (2 * ((m + 2 : ℕ) : ℝ)) =
      Real.sqrt 2 * Real.sqrt ((m + 2 : ℕ) : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hsqrt, div_pow]
  have hpos : (0 : ℝ) < Real.sqrt 2 * Real.sqrt ((m + 2 : ℕ) : ℝ) *
      (((m + 2 : ℕ) : ℝ) ^ (m + 2) / Real.exp 1 ^ (m + 2)) := by
    positivity
  have he : Real.exp 1 ^ (m + 2) = Real.exp 1 ^ (m + 1) * Real.exp 1 := by
    rw [pow_succ]
  calc Stirling.stirlingSeq (m + 2) *
        (Real.sqrt 2 * Real.sqrt ((m + 2 : ℕ) : ℝ) *
          (((m + 2 : ℕ) : ℝ) ^ (m + 2) / Real.exp 1 ^ (m + 2)))
      < (Real.exp 1 / Real.sqrt 2) *
          (Real.sqrt 2 * Real.sqrt ((m + 2 : ℕ) : ℝ) *
            (((m + 2 : ℕ) : ℝ) ^ (m + 2) / Real.exp 1 ^ (m + 2))) := by
        apply mul_lt_mul_of_pos_right hlt hpos
    _ = Real.sqrt ((m + 2 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) ^ (m + 2) /
        Real.exp 1 ^ (m + 2 - 1) := by
        rw [show m + 2 - 1 = m + 1 by omega, he]; field_simp

/-- The second inequality of ATLAS `NumberTheoryI` Corollary 14.26, as a
statement about the degree `n` and the number `s` of complex places:
the Minkowski-type term strictly exceeds the exponential term. -/
theorem pow_div_factorial_sq_mul_pi_div_four_pow_gt (n s : ℕ) (hn : n ≠ 0)
    (hs : 2 * s ≤ n) :
    (1 / (Real.exp 1 ^ 2 * n)) * ((Real.pi * Real.exp 1 ^ 2) / 4) ^ n
      < ((n : ℝ) ^ n / (Nat.factorial n : ℝ)) ^ 2 *
          (Real.pi / 4) ^ (2 * s) := by
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hfact_pos : (0 : ℝ) < (Nat.factorial n : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hpow_pos : (0 : ℝ) < (n : ℝ) ^ n := pow_pos hnR n
  have hsqrt_pos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hexp_pos : (0 : ℝ) < Real.exp 1 ^ (n - 1) :=
    pow_pos (Real.exp_pos 1) _
  have hpi_pos : (0 : ℝ) < Real.pi / 4 := by positivity
  have hpi_lt_one : Real.pi / 4 < 1 := by
    rw [div_lt_one (by norm_num : (0 : ℝ) < 4)]; exact Real.pi_lt_four
  -- Ratio lower bounds from the factorial bounds.
  have hratio : Real.exp 1 ^ (n - 1) / Real.sqrt n ≤
      (n : ℝ) ^ n / (Nat.factorial n : ℝ) := by
    rw [div_le_div_iff₀ hsqrt_pos hfact_pos]
    have hf := factorial_le_sqrt_mul_pow_div_exp n hn
    rw [le_div_iff₀ hexp_pos] at hf
    calc Real.exp 1 ^ (n - 1) * (Nat.factorial n : ℝ)
        = (Nat.factorial n : ℝ) * Real.exp 1 ^ (n - 1) := by ring
      _ ≤ Real.sqrt n * (n : ℝ) ^ n := hf
      _ = (n : ℝ) ^ n * Real.sqrt n := by ring
  have hsq : (Real.exp 1 ^ (n - 1) / Real.sqrt n) ^ 2 ≤
      ((n : ℝ) ^ n / (Nat.factorial n : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hratio 2
  have hsq_eq : (Real.exp 1 ^ (n - 1) / Real.sqrt n) ^ 2 =
      Real.exp 1 ^ (2 * (n - 1)) / n := by
    rw [div_pow, Real.sq_sqrt hnR.le, ← pow_mul, mul_comm]
  -- The exponential term equals the reduced lower bound.
  have hB_eq : (1 / (Real.exp 1 ^ 2 * n)) *
        ((Real.pi * Real.exp 1 ^ 2) / 4) ^ n
      = (Real.exp 1 ^ (2 * (n - 1)) / n) * (Real.pi / 4) ^ n := by
    have hexp2 : Real.exp 1 ^ (2 * n) =
        Real.exp 1 ^ (2 * (n - 1)) * Real.exp 1 ^ 2 := by
      rw [← pow_add]; congr 1; omega
    have hpi : ((Real.pi * Real.exp 1 ^ 2) / 4) ^ n =
        (Real.pi / 4) ^ n * Real.exp 1 ^ (2 * n) := by
      rw [show Real.pi * Real.exp 1 ^ 2 / 4 =
        (Real.pi / 4) * Real.exp 1 ^ 2 by ring, mul_pow, ← pow_mul]
    rw [hpi, hexp2]
    field_simp
  rw [hB_eq]
  rcases lt_or_eq_of_le hs with hlt | heq
  · -- `2 * s < n`: the `(π / 4)` factor alone gives strictness.
    have hpi_lt : (Real.pi / 4) ^ n < (Real.pi / 4) ^ (2 * s) :=
      pow_lt_pow_right_of_lt_one₀ hpi_pos hpi_lt_one hlt
    calc (Real.exp 1 ^ (2 * (n - 1)) / n) * (Real.pi / 4) ^ n
        < (Real.exp 1 ^ (2 * (n - 1)) / n) * (Real.pi / 4) ^ (2 * s) := by
          apply mul_lt_mul_of_pos_left hpi_lt (by positivity)
      _ ≤ ((n : ℝ) ^ n / (Nat.factorial n : ℝ)) ^ 2 *
          (Real.pi / 4) ^ (2 * s) := by
          rw [← hsq_eq]
          exact mul_le_mul_of_nonneg_right hsq (by positivity)
  · -- `2 * s = n`: need the strict factorial bound; then `n ≥ 2`.
    have hn2 : 2 ≤ n := by omega
    have hratio' : Real.exp 1 ^ (n - 1) / Real.sqrt n <
        (n : ℝ) ^ n / (Nat.factorial n : ℝ) := by
      rw [div_lt_div_iff₀ hsqrt_pos hfact_pos]
      have hf := factorial_lt_sqrt_mul_pow_div_exp n hn2
      rw [lt_div_iff₀ hexp_pos] at hf
      calc Real.exp 1 ^ (n - 1) * (Nat.factorial n : ℝ)
          = (Nat.factorial n : ℝ) * Real.exp 1 ^ (n - 1) := by ring
        _ < Real.sqrt n * (n : ℝ) ^ n := hf
        _ = (n : ℝ) ^ n * Real.sqrt n := by ring
    have hsq' : (Real.exp 1 ^ (n - 1) / Real.sqrt n) ^ 2 <
        ((n : ℝ) ^ n / (Nat.factorial n : ℝ)) ^ 2 :=
      pow_lt_pow_left₀ hratio' (by positivity) (by norm_num : 2 ≠ 0)
    have hpi_eq : (Real.pi / 4) ^ (2 * s) = (Real.pi / 4) ^ n := by
      rw [heq]
    rw [hpi_eq]
    calc (Real.exp 1 ^ (2 * (n - 1)) / n) * (Real.pi / 4) ^ n
        = (Real.exp 1 ^ (n - 1) / Real.sqrt n) ^ 2 * (Real.pi / 4) ^ n := by
          rw [hsq_eq]
      _ < ((n : ℝ) ^ n / (Nat.factorial n : ℝ)) ^ 2 * (Real.pi / 4) ^ n := by
          exact mul_lt_mul_of_pos_right hsq' (pow_pos hpi_pos _)

/-- The first inequality of ATLAS `NumberTheoryI` Corollary 14.26:
the Minkowski-type term is at most `|D_K|`. This is Mathlib's
`NumberField.abs_discr_ge'`, restated in the form used by the book. -/
theorem middle_term_le_abs_discr (K : Type*) [Field K] [NumberField K] :
    (((Module.finrank ℚ K : ℝ) ^ (Module.finrank ℚ K) /
      (Nat.factorial (Module.finrank ℚ K) : ℝ)) ^ 2 *
      (Real.pi / 4) ^ (2 * nrComplexPlaces K)) ≤ (↑|discr K| : ℝ) := by
  have h := abs_discr_ge' K
  have h1 : (Real.pi / 4) ^ (2 * nrComplexPlaces K) =
      ((4 / Real.pi) ^ (2 * nrComplexPlaces K))⁻¹ := by
    rw [← inv_pow, inv_div]
  have h2 : (((Module.finrank ℚ K : ℝ) ^ (Module.finrank ℚ K) /
      (Nat.factorial (Module.finrank ℚ K) : ℝ)) ^ 2) =
      (Module.finrank ℚ K : ℝ) ^ (2 * Module.finrank ℚ K) /
        (Nat.factorial (Module.finrank ℚ K) : ℝ) ^ 2 := by
    rw [div_pow, ← pow_mul, mul_comm]
  have hmid : (((Module.finrank ℚ K : ℝ) ^ (Module.finrank ℚ K) /
      (Nat.factorial (Module.finrank ℚ K) : ℝ)) ^ 2 *
      (Real.pi / 4) ^ (2 * nrComplexPlaces K))
      = (Module.finrank ℚ K : ℝ) ^ (2 * Module.finrank ℚ K) /
        ((4 / Real.pi) ^ (2 * nrComplexPlaces K) *
          (Nat.factorial (Module.finrank ℚ K) : ℝ) ^ 2) := by
    rw [h1, h2]
    field_simp
  rw [hmid]
  exact h

/-- ATLAS `NumberTheoryI` Corollary 14.26 (second inequality): the
absolute discriminant of a number field of degree `n` exceeds
`(π e ^ 2 / 4) ^ n / (e ^ 2 * n)`, so it grows at least exponentially
in the degree. -/
theorem abs_discr_gt_exp_term (K : Type*) [Field K] [NumberField K] :
    (1 / (Real.exp 1 ^ 2 * Module.finrank ℚ K)) *
      ((Real.pi * Real.exp 1 ^ 2) / 4) ^ (Module.finrank ℚ K) <
        (↑|discr K| : ℝ) := by
  have h2s : 2 * nrComplexPlaces K ≤ Module.finrank ℚ K := by
    have h := InfinitePlace.card_add_two_mul_card_eq_rank K
    omega
  exact lt_of_lt_of_le
    (pow_div_factorial_sq_mul_pi_div_four_pow_gt (Module.finrank ℚ K)
      (nrComplexPlaces K) (ne_of_gt (Module.finrank_pos)) h2s)
    (middle_term_le_abs_discr K)

end NumberField
