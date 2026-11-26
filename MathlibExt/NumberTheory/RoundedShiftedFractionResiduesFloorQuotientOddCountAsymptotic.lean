/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import MathlibExt.NumberTheory.AlternatingReciprocalIntegral
public import MathlibExt.NumberTheory.AlternatingSumFloorDiv
public import MathlibExt.NumberTheory.CeilQuotientOddCount
public import MathlibExt.NumberTheory.DivisorCountBound
public import MathlibExt.NumberTheory.FloorDivisionCounts
public import MathlibExt.NumberTheory.FloorQuotientDivisorSummatory
public import MathlibExt.NumberTheory.FloorQuotientOddCount
public import MathlibExt.NumberTheory.Harmonic.EulerMascheroniBounds
public import MathlibExt.NumberTheory.RoundQuotientOddCount
public import MathlibExt.NumberTheory.RoundedQuotientThresholdCounts
public import MathlibExt.NumberTheory.ShiftedFloorThresholdCounts

/-!
# Asymptotics of the floor parity count

`floorQuotientOddCount_asymptotic` states that the floor parity count `F n` satisfies
`|F n - n log 2| ≤ C * sqrt n` for some real constant `C` and every `n ≥ 1`, and that
`F n / n` tends to `log 2`. The proof combines the alternating-sum formula for the count
with the alternating floor-sum estimate and a convergence rate for the alternating
harmonic series derived from the Euler-Mascheroni bounds.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 7 (`jis-2024-24.2.5-prop-7`).
-/

namespace MetaMathlibExt

@[expose] public section

open Filter Topology

private theorem filter_range_eq_self (n : ℕ) :
    (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ (n : ℝ) - 0) =
      Finset.range (n + 1) := by
  apply Finset.filter_true_of_mem
  intro k hk
  simp only [Finset.mem_range] at hk
  have hkn : k ≤ n := by omega
  have hcast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  linarith

private theorem floorQuotientOddCount_real_eq_sum_range (n : ℕ) :
    (floorQuotientOddCount n : ℝ) =
      ∑ k ∈ Finset.range n, ((n / (k + 1) : ℕ) : ℝ) * (-1 : ℝ) ^ k := by
  have hcast : (floorQuotientOddCount n : ℝ) =
      ∑ d ∈ Finset.Icc 1 n, ((n / d : ℕ) : ℝ) * (-1 : ℝ) ^ (d + 1) := by
    have h2 := floorQuotientOddCount_eq_alternating_sum n
    have h := congrArg (fun z : ℤ => (z : ℝ)) h2
    simpa only [Int.cast_natCast, Int.cast_sum, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one] using h
  rw [hcast, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro k _
  rw [add_comm 1 k]
  congr 1
  have hkk : k + 1 + 1 = k + 2 := by ring
  rw [hkk, pow_add]
  have h2 : (-1 : ℝ) ^ (2 : ℕ) = 1 := by norm_num
  rw [h2, mul_one]

private def shiftSucc : ℕ → ℝ := fun k => (k : ℝ) + 1

private theorem shiftSucc_strictMono : StrictMono shiftSucc := by
  intro a b hab
  change (a : ℝ) + 1 < (b : ℝ) + 1
  have h : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  linarith

private theorem shiftSucc_ge_one : ∀ k, 1 ≤ shiftSucc k := by
  intro k
  change 1 ≤ (k : ℝ) + 1
  have h : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

private theorem shiftSucc_ge_self : ∀ k : ℕ, (k : ℝ) ≤ shiftSucc k := by
  intro k
  change (k : ℝ) ≤ (k : ℝ) + 1
  linarith [zero_le_one (α := ℝ)]

private theorem prop32LHS_eq_sum_range (n : ℕ) :
    (∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ (n : ℝ) - 0),
        (⌊((n : ℝ) - 0) / shiftSucc k⌋ : ℝ) * (-1 : ℝ) ^ k) =
      ∑ k ∈ Finset.range (n + 1), ((n / (k + 1) : ℕ) : ℝ) * (-1 : ℝ) ^ k := by
  rw [filter_range_eq_self]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have hbk : shiftSucc k = (((k + 1 : ℕ)) : ℝ) := by
    change (k : ℝ) + 1 = _
    push_cast
    ring
  have hsub : ((n : ℝ) - 0) = (n : ℝ) := sub_zero _
  rw [hsub, hbk]
  have hfl : ⌊(n : ℝ) / (((k + 1 : ℕ)) : ℝ)⌋ = ((n / (k + 1) : ℕ) : ℤ) := by
    rw [Int.floor_div_natCast, Int.floor_natCast]
    rfl
  rw [hfl]
  norm_cast

private theorem sum_range_succ_natdiv_eq (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ((n / (k + 1) : ℕ) : ℝ) * (-1 : ℝ) ^ k) =
      ∑ k ∈ Finset.range n, ((n / (k + 1) : ℕ) : ℝ) * (-1 : ℝ) ^ k := by
  rw [Finset.sum_range_succ]
  have hdiv : n / (n + 1) = 0 := Nat.div_eq_of_lt (Nat.lt_succ_self n)
  have hterm : ((n / (n + 1) : ℕ) : ℝ) * (-1 : ℝ) ^ n = 0 := by
    rw [hdiv, Nat.cast_zero, zero_mul]
  rw [hterm, add_zero]

private noncomputable def altHarmonic (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k / ((k : ℝ) + 1)

private theorem altHarmonic_succ (N : ℕ) :
    altHarmonic (N + 1) = altHarmonic N + (-1 : ℝ) ^ N / ((N : ℝ) + 1) := by
  simp [altHarmonic, Finset.sum_range_succ]

private theorem harmonic_succ_real (n : ℕ) :
    (harmonic (n + 1) : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) := by
  rw [harmonic_succ]
  push_cast
  ring

private theorem altHarmonic_two_mul (m : ℕ) :
    altHarmonic (2 * m) = (harmonic (2 * m) : ℝ) - (harmonic m : ℝ) := by
  induction m with
  | zero => simp [altHarmonic]
  | succ m ih =>
    have h2 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    rw [h2, altHarmonic_succ, altHarmonic_succ]
    rw [harmonic_succ_real (2 * m + 1), harmonic_succ_real (2 * m), harmonic_succ_real m]
    rw [ih]
    have heven : (-1 : ℝ) ^ (2 * m) = 1 := by
      rw [pow_mul]
      simp
    have hodd : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
      rw [pow_succ, heven, one_mul]
    rw [heven, hodd]
    push_cast
    have h2m : ((2 : ℝ) + (m : ℝ) * 2) = 2 * ((1 : ℝ) + (m : ℝ)) := by ring
    have hinv : (1 : ℝ) / ((1 : ℝ) + (m : ℝ)) = 2 / ((2 : ℝ) + (m : ℝ) * 2) := by
      rw [h2m]
      field_simp
    have heq1 : (2 : ℝ) * (m : ℝ) + 1 + 1 = 2 + (m : ℝ) * 2 := by ring
    have heq2 : (m : ℝ) + 1 = 1 + (m : ℝ) := by ring
    rw [heq1, heq2]
    simp only [div_eq_mul_inv, one_mul] at hinv ⊢
    linarith [hinv]

private theorem log_two_mul_sub_log (m : ℕ) (hm : 1 ≤ m) :
    Real.log ((2 * m : ℕ) : ℝ) - Real.log (m : ℝ) = Real.log 2 := by
  have h2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  rw [h2m, Real.log_mul (by norm_num) (by positivity)]
  ring

private theorem altHarmonic_even_bound (m : ℕ) (hm : 1 ≤ m) :
    |altHarmonic (2 * m) - Real.log 2| ≤ 3 / (m : ℝ) := by
  rw [altHarmonic_two_mul]
  have h2m1 : 1 ≤ 2 * m := by omega
  have e1 := Real.abs_harmonic_sub_log_sub_eulerMascheroniConstant_le h2m1
  have e2 := Real.abs_harmonic_sub_log_sub_eulerMascheroniConstant_le hm
  have hlog := log_two_mul_sub_log m hm
  have hdecomp : ((harmonic (2 * m) : ℝ) - (harmonic m : ℝ)) - Real.log 2 =
      ((harmonic (2 * m) : ℝ) - Real.log ((2 * m : ℕ) : ℝ) - Real.eulerMascheroniConstant) -
      ((harmonic m : ℝ) - Real.log (m : ℝ) - Real.eulerMascheroniConstant) +
      (Real.log ((2 * m : ℕ) : ℝ) - Real.log (m : ℝ) - Real.log 2) := by
    ring
  rw [hdecomp]
  have hz : Real.log ((2 * m : ℕ) : ℝ) - Real.log (m : ℝ) - Real.log 2 = 0 := by
    linarith [hlog]
  rw [hz, add_zero]
  have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hle : ((m : ℝ)) ≤ (((2 * m : ℕ) : ℝ)) := by
    have hle2 : (m : ℝ) ≤ 2 * (m : ℝ) := by linarith
    have hcast : (((2 * m : ℕ) : ℝ)) = 2 * (m : ℝ) := by push_cast; ring
    linarith
  have hinv_le : (1 : ℝ) / (((2 * m : ℕ) : ℝ)) ≤ 1 / (m : ℝ) :=
    one_div_le_one_div_of_le hpos hle
  have h1m : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have h3eq : (3 : ℝ) / (m : ℝ) = 1 / (m : ℝ) + 1 / (m : ℝ) + 1 / (m : ℝ) := by
    field_simp
    ring
  calc |_ - _| ≤ |(harmonic (2*m) : ℝ) - Real.log ((2*m : ℕ) : ℝ) - Real.eulerMascheroniConstant| +
          |(harmonic m : ℝ) - Real.log (m : ℝ) - Real.eulerMascheroniConstant| := abs_sub _ _
    _ ≤ 1 / (((2*m : ℕ) : ℝ)) + 1 / (m : ℝ) := add_le_add e1 e2
    _ ≤ 3 / (m : ℝ) := by rw [h3eq]; linarith [hinv_le, h1m]

private theorem altHarmonic_one : altHarmonic 1 = 1 := by
  simp [altHarmonic]

private theorem altHarmonic_odd_succ (m : ℕ) :
    altHarmonic (2 * m + 1) = altHarmonic (2 * m) + 1 / (((2 * m : ℕ) : ℝ) + 1) := by
  have h : 2 * m + 1 = (2 * m) + 1 := rfl
  rw [h, altHarmonic_succ]
  have heven : (-1 : ℝ) ^ (2 * m) = 1 := by
    rw [pow_mul]
    simp
  rw [heven]

private theorem altHarmonic_odd_bound (m : ℕ) (hm : 1 ≤ m) :
    |altHarmonic (2 * m + 1) - Real.log 2| ≤ 10 / (((2 * m + 1 : ℕ) : ℝ)) := by
  rw [altHarmonic_odd_succ]
  have hev := altHarmonic_even_bound m hm
  have hposm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hposN : (0 : ℝ) < (((2 * m + 1 : ℕ) : ℝ)) := by positivity
  have hcastN : (((2 * m + 1 : ℕ) : ℝ)) = 2 * (m : ℝ) + 1 := by push_cast; ring
  have h3le9 : (3 : ℝ) / (m : ℝ) ≤ 9 / (((2 * m + 1 : ℕ) : ℝ)) := by
    rw [div_le_div_iff₀ hposm hposN]
    rw [hcastN]
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have h10eq : (9 : ℝ) / (((2 * m + 1 : ℕ) : ℝ)) + 1 / (((2 * m + 1 : ℕ) : ℝ)) =
      10 / (((2 * m + 1 : ℕ) : ℝ)) := by
    rw [← add_div]
    norm_num
  have hstep : |altHarmonic (2 * m) + 1 / (((2 * m : ℕ) : ℝ) + 1) - Real.log 2| ≤
      3 / (m : ℝ) + 1 / (((2 * m + 1 : ℕ) : ℝ)) := by
    have hcast1 : (((2 * m : ℕ) : ℝ) + 1) = (((2 * m + 1 : ℕ) : ℝ)) := by
      push_cast; ring
    rw [hcast1]
    calc |altHarmonic (2*m) + 1/(((2*m+1 : ℕ):ℝ)) - Real.log 2|
        = |(altHarmonic (2*m) - Real.log 2) + 1/(((2*m+1 : ℕ):ℝ))| := by ring_nf
      _ ≤ |altHarmonic (2*m) - Real.log 2| + |1/(((2*m+1 : ℕ):ℝ))| := abs_add_le _ _
      _ = |altHarmonic (2*m) - Real.log 2| + 1/(((2*m+1 : ℕ):ℝ)) := by
          rw [abs_of_pos (one_div_pos.mpr hposN)]
      _ ≤ 3/(m:ℝ) + 1/(((2*m+1 : ℕ):ℝ)) := add_le_add hev le_rfl
  calc |altHarmonic (2*m) + 1/(((2*m : ℕ):ℝ)+1) - Real.log 2|
      ≤ 3/(m:ℝ) + 1/(((2*m+1 : ℕ):ℝ)) := hstep
    _ ≤ 9/(((2*m+1 : ℕ):ℝ)) + 1/(((2*m+1 : ℕ):ℝ)) := add_le_add h3le9 le_rfl
    _ = 10/(((2*m+1 : ℕ):ℝ)) := h10eq

private theorem altHarmonic_bound (N : ℕ) (hN : 1 ≤ N) :
    |altHarmonic N - Real.log 2| ≤ 10 / (N : ℝ) := by
  rcases Nat.even_or_odd N with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hm1 : 1 ≤ m := by omega
    have heq : m + m = 2 * m := by ring
    rw [heq]
    have hev := altHarmonic_even_bound m hm1
    have hcast : (((2 * m : ℕ) : ℝ)) = 2 * (m : ℝ) := by push_cast; ring
    have h10eq : (10 : ℝ) / (((2 * m : ℕ) : ℝ)) = 5 / (m : ℝ) := by
      rw [hcast]
      field_simp
      ring
    rw [h10eq]
    have h1m : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
    have h5eq : (5 : ℝ) / (m : ℝ) = 3 / (m : ℝ) + 1 / (m : ℝ) + 1 / (m : ℝ) := by
      field_simp
      ring
    rw [h5eq]
    linarith [hev, h1m]
  · rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · have h10 : (2 * 0 + 1 : ℕ) = 1 := by norm_num
      rw [h10, altHarmonic_one]
      have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlog_lt : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
      have habs : |(1 : ℝ) - Real.log 2| = 1 - Real.log 2 := abs_of_pos (by linarith)
      rw [habs]
      simp
      linarith
    · exact altHarmonic_odd_bound m hmpos

private theorem prop32RHS_eq_altHarmonic (n : ℕ) :
    (∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ (n : ℝ) - 0),
        (-1 : ℝ) ^ k / shiftSucc k) = altHarmonic (n + 1) := by
  rw [filter_range_eq_self]
  rfl

private theorem main_bound :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(floorQuotientOddCount n : ℝ) - n * Real.log 2| ≤ C * Real.sqrt n := by
  obtain ⟨C₀, hC₀⟩ := alternating_sum_floor_div_eq_add_bigO (0 : ℝ) le_rfl
    zero_lt_one shiftSucc shiftSucc_strictMono shiftSucc_ge_one shiftSucc_ge_self
  refine ⟨C₀ + 10, fun n hn => ?_⟩
  have hprop := hC₀ n hn
  rw [prop32LHS_eq_sum_range, sum_range_succ_natdiv_eq,
    ← floorQuotientOddCount_real_eq_sum_range, prop32RHS_eq_altHarmonic] at hprop
  have halt_bd := altHarmonic_bound (n + 1) (Nat.succ_pos n)
  have hnpos1 : (0 : ℝ) < (((n + 1 : ℕ)) : ℝ) := by positivity
  have hfrac : (n : ℝ) / (((n + 1 : ℕ)) : ℝ) ≤ 1 :=
    (div_le_one hnpos1).mpr (by exact_mod_cast Nat.le_succ n)
  have h10 : (n : ℝ) * (10 / (((n + 1 : ℕ)) : ℝ)) ≤ 10 := by
    have heq : (n : ℝ) * (10 / (((n + 1 : ℕ)) : ℝ)) =
        10 * ((n : ℝ) / (((n + 1 : ℕ)) : ℝ)) := by ring
    rw [heq]
    calc 10 * ((n : ℝ) / (((n + 1 : ℕ)) : ℝ)) ≤ 10 * 1 :=
            mul_le_mul_of_nonneg_left hfrac (by norm_num)
      _ = 10 := mul_one _
  have hB : |(n : ℝ) * (altHarmonic (n + 1) - Real.log 2)| ≤ 10 := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    calc (n : ℝ) * |altHarmonic (n + 1) - Real.log 2|
        ≤ (n : ℝ) * (10 / (((n + 1 : ℕ)) : ℝ)) :=
          mul_le_mul_of_nonneg_left halt_bd (Nat.cast_nonneg n)
      _ ≤ 10 := h10
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have h10sqrt : (10 : ℝ) ≤ 10 * Real.sqrt n := by
    have h := mul_le_mul_of_nonneg_left hsqrt1 (show (0 : ℝ) ≤ 10 by norm_num)
    rwa [mul_one] at h
  have hdecomp : (floorQuotientOddCount n : ℝ) - (n : ℝ) * Real.log 2 =
      ((floorQuotientOddCount n : ℝ) - (n : ℝ) * altHarmonic (n + 1)) +
        (n : ℝ) * (altHarmonic (n + 1) - Real.log 2) := by ring
  rw [hdecomp]
  calc |_ + _| ≤ |(floorQuotientOddCount n : ℝ) - (n : ℝ) * altHarmonic (n + 1)| +
          |(n : ℝ) * (altHarmonic (n + 1) - Real.log 2)| := abs_add_le _ _
    _ ≤ C₀ * Real.sqrt n + 10 := add_le_add hprop hB
    _ ≤ C₀ * Real.sqrt n + 10 * Real.sqrt n := add_le_add le_rfl h10sqrt
    _ = (C₀ + 10) * Real.sqrt n := by ring

private theorem main_tendsto (C : ℝ) (hC : ∀ n : ℕ, 1 ≤ n →
    |(floorQuotientOddCount n : ℝ) - n * Real.log 2| ≤ C * Real.sqrt n) :
    Tendsto (fun n : ℕ => (floorQuotientOddCount n : ℝ) / n) atTop
      (𝓝 (Real.log 2)) := by
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖(floorQuotientOddCount n : ℝ) / n - Real.log 2‖ ≤ C / Real.sqrt n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h := hC n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsqrtpos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    rw [Real.norm_eq_abs]
    have heq : (floorQuotientOddCount n : ℝ) / (n : ℝ) - Real.log 2 =
        ((floorQuotientOddCount n : ℝ) - (n : ℝ) * Real.log 2) / (n : ℝ) := by
      field_simp
    rw [heq, abs_div, abs_of_pos hnpos]
    have hsqrt_eq : Real.sqrt (n : ℝ) / (n : ℝ) = 1 / Real.sqrt (n : ℝ) := by
      have h1 : (n : ℝ) ≠ 0 := hnpos.ne'
      have h2 : Real.sqrt (n : ℝ) ≠ 0 := hsqrtpos.ne'
      have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
      field_simp
      rw [pow_two] at hsq
      linarith
    have heq2 : C * Real.sqrt (n : ℝ) / (n : ℝ) = C / Real.sqrt (n : ℝ) := by
      rw [mul_div_assoc, hsqrt_eq, one_div, ← div_eq_mul_inv]
    calc |(floorQuotientOddCount n : ℝ) - (n : ℝ) * Real.log 2| / (n : ℝ)
        ≤ C * Real.sqrt (n : ℝ) / (n : ℝ) :=
          (div_le_div_iff_of_pos_right hnpos).mpr h
      _ = C / Real.sqrt (n : ℝ) := heq2
  have htend : Tendsto (fun n : ℕ => C / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
    have hsqrt_top : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ))) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => (Real.sqrt ((n : ℝ)))⁻¹) atTop (𝓝 0) :=
      hsqrt_top.inv_tendsto_atTop
    have heq : (fun n : ℕ => C / Real.sqrt ((n : ℝ))) =
        fun n : ℕ => C * (Real.sqrt ((n : ℝ)))⁻¹ := by
      funext n
      rw [div_eq_mul_inv]
    rw [heq]
    simpa using hinv.const_mul C
  have hzero : Tendsto (fun n : ℕ => (floorQuotientOddCount n : ℝ) / n - Real.log 2)
      atTop (𝓝 0) :=
    squeeze_zero_norm' hbound htend
  have hconst : Tendsto (fun _ : ℕ => Real.log 2) atTop (𝓝 (Real.log 2)) :=
    tendsto_const_nhds
  have hlim := hzero.add hconst
  rw [zero_add] at hlim
  have hfun : (fun n : ℕ => (floorQuotientOddCount n : ℝ) / (n : ℝ)) =
      fun n : ℕ => ((floorQuotientOddCount n : ℝ) / n - Real.log 2) + Real.log 2 := by
    funext n
    ring
  rw [hfun]
  exact hlim

/-- **Asymptotics of the floor parity count.** Let $\mathcal{F}_n$ be the number of integers $k$
with $1 \le k \le n$ for which $\lfloor n/k \rfloor$ is odd. There is a real constant $C$ such
that $|\mathcal{F}_n - n \log 2| \le C \sqrt{n}$ for every integer $n \ge 1$, and
$\mathcal{F}_n / n \to \log 2$ as $n \to \infty$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 7 (`jis-2024-24.2.5-prop-7`). -/
public theorem floorQuotientOddCount_asymptotic :
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(floorQuotientOddCount n : ℝ) - n * Real.log 2| ≤ C * Real.sqrt n) ∧
    Tendsto (fun n : ℕ => (floorQuotientOddCount n : ℝ) / n) atTop
      (𝓝 (Real.log 2))
    := by
  obtain ⟨C, hC⟩ := main_bound
  exact ⟨⟨C, hC⟩, main_tendsto C hC⟩

end

end MetaMathlibExt
