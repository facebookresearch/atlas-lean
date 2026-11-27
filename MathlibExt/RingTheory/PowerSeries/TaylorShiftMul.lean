/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_PowerSeries_taylorShift_mul.lean`
and
`P2M/Sol/S_PowerSeries_taylorShift_mul.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Ultra
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Order

@[expose] public section

namespace PowerSeries

variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]

private theorem norm_coeff_le (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (n : ℕ) :
    ‖PowerSeries.coeff n F‖ ≤ M / ρ ^ n :=
  (le_div_iff₀ (pow_pos hρ n)).mpr (hF n)

private theorem bound_nonneg (F : PowerSeries L) {ρ M : ℝ}
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) : 0 ≤ M := by
  have h := hF 0
  simp only [pow_zero, mul_one] at h
  exact (norm_nonneg _).trans h

private theorem norm_term_le (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (a : L) (ha : ‖a‖ < ρ) (j m : ℕ) :
    ‖PowerSeries.coeff (j + m) F * a ^ m‖ ≤ M / ρ ^ j * (‖a‖ / ρ) ^ m := by
  rw [norm_mul, norm_pow, div_pow]
  have h1 := norm_coeff_le F hρ hF (j + m)
  rw [pow_add] at h1
  calc ‖PowerSeries.coeff (j + m) F‖ * ‖a‖ ^ m
      ≤ M / (ρ ^ j * ρ ^ m) * ‖a‖ ^ m := by gcongr
    _ = M / ρ ^ j * (‖a‖ ^ m / ρ ^ m) := by field_simp

private theorem norm_shift_term_le (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (a : L) (ha : ‖a‖ < ρ) (n k : ℕ) :
    ‖PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k‖
      ≤ M / ρ ^ n * (‖a‖ / ρ) ^ k := by
  have h := norm_term_le F hρ hF a ha n k
  rw [norm_mul, norm_mul]
  rw [norm_mul] at h
  have hc : ‖((n + k).choose n : L)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one L _
  calc ‖PowerSeries.coeff (n + k) F‖ * ‖((n + k).choose n : L)‖ * ‖a ^ k‖
      ≤ ‖PowerSeries.coeff (n + k) F‖ * 1 * ‖a ^ k‖ := by gcongr
    _ = ‖PowerSeries.coeff (n + k) F‖ * ‖a ^ k‖ := by rw [mul_one]
    _ ≤ M / ρ ^ n * (‖a‖ / ρ) ^ k := h

private theorem summable_shifted (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (a : L) (ha : ‖a‖ < ρ) (j : ℕ) :
    Summable (fun m : ℕ => PowerSeries.coeff (j + m) F * a ^ m) := by
  have hr : ‖a‖ / ρ < 1 := (div_lt_one hρ).mpr ha
  have hr0 : 0 ≤ ‖a‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  exact Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr).mul_left (M / ρ ^ j))
    (fun m => norm_term_le F hρ hF a ha j m)

private theorem norm_tsum_shifted_le (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (a : L) (ha : ‖a‖ < ρ) (j : ℕ) :
    ‖∑' m : ℕ, PowerSeries.coeff (j + m) F * a ^ m‖ ≤ M / ρ ^ j := by
  have hM := bound_nonneg F hF
  have hC : 0 ≤ M / ρ ^ j := div_nonneg hM (pow_pos hρ j).le
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC fun m => ?_
  have hr1 : (‖a‖ / ρ) ^ m ≤ 1 :=
    pow_le_one₀ (div_nonneg (norm_nonneg _) hρ.le) ((div_le_one hρ).mpr ha.le)
  calc ‖PowerSeries.coeff (j + m) F * a ^ m‖
      ≤ M / ρ ^ j * (‖a‖ / ρ) ^ m := norm_term_le F hρ hF a ha j m
    _ ≤ M / ρ ^ j * 1 := by gcongr
    _ = M / ρ ^ j := mul_one _

private theorem summable_and_norm_tsum_coeff_mul_pow_le (F : PowerSeries L) {ρ M : ℝ}
    (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (z : L) (hz : ‖z‖ < ρ) :
    Summable (fun n => PowerSeries.coeff n F * z ^ n)
      ∧ ‖∑' n, PowerSeries.coeff n F * z ^ n‖ ≤ M := by
  have h1 := summable_shifted F hρ hF z hz 0
  have h2 := norm_tsum_shifted_le F hρ hF z hz 0
  simp only [zero_add, pow_zero, div_one] at h1 h2
  exact ⟨h1, h2⟩

private theorem norm_coeff_mul_mul_pow_le (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 ≤ ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M') (n : ℕ) :
    ‖PowerSeries.coeff n (F * G)‖ * ρ ^ n ≤ M * M' := by
  have hM := bound_nonneg F hF
  have hM' := bound_nonneg G hG
  rw [PowerSeries.coeff_mul]
  rcases (pow_nonneg hρ n).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact mul_nonneg hM hM'
  have hC : 0 ≤ M * M' / ρ ^ n := div_nonneg (mul_nonneg hM hM') hpos.le
  have h : ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G‖ ≤ M * M' / ρ ^ n := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [norm_mul, le_div_iff₀ hpos, ← hp, pow_add]
    calc ‖PowerSeries.coeff p.1 F‖ * ‖PowerSeries.coeff p.2 G‖ * (ρ ^ p.1 * ρ ^ p.2)
        = (‖PowerSeries.coeff p.1 F‖ * ρ ^ p.1) * (‖PowerSeries.coeff p.2 G‖ * ρ ^ p.2) := by
          ring
      _ ≤ M * M' := mul_le_mul (hF p.1) (hG p.2) (by positivity) hM
  exact (le_div_iff₀ hpos).mp h

private theorem tsum_coeff_mul_mul_pow_eq_of_norm_lt (F G : PowerSeries L) {ρ M M' : ℝ}
    (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M') (z : L) (hz : ‖z‖ < ρ) :
    ∑' n, PowerSeries.coeff n (F * G) * z ^ n
      = (∑' n, PowerSeries.coeff n F * z ^ n) * ∑' n, PowerSeries.coeff n G * z ^ n := by
  have hr : ‖z‖ / ρ < 1 := (div_lt_one hρ).mpr hz
  have hr0 : 0 ≤ ‖z‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  have hFn : Summable (fun n => ‖PowerSeries.coeff n F * z ^ n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one hr0 hr).mul_left (M / ρ ^ 0))
    simpa using norm_term_le F hρ hF z hz 0 n
  have hGn : Summable (fun n => ‖PowerSeries.coeff n G * z ^ n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one hr0 hr).mul_left (M' / ρ ^ 0))
    simpa using norm_term_le G hρ hG z hz 0 n
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hFn hGn]
  refine tsum_congr fun n => ?_
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, pow_add]
  ring

private theorem norm_coeff_taylorShift_mul_pow_le (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (a : L) (ha : ‖a‖ < ρ) (n : ℕ) :
    Summable (fun k : ℕ => PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k) ∧
      ‖PowerSeries.coeff n (PowerSeries.mk fun n => ∑' k : ℕ,
          PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k)‖ * ρ ^ n ≤ M := by
  have hr : ‖a‖ / ρ < 1 := (div_lt_one hρ).mpr ha
  have hr0 : 0 ≤ ‖a‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  have hsum : Summable (fun k : ℕ =>
      PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr).mul_left (M / ρ ^ n))
      (fun k => norm_shift_term_le F hρ hF a ha n k)
  refine ⟨hsum, ?_⟩
  rw [PowerSeries.coeff_mk]
  have hM := bound_nonneg F hF
  have hC : 0 ≤ M / ρ ^ n := div_nonneg hM (pow_pos hρ n).le
  have h : ‖∑' k : ℕ, PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k‖
      ≤ M / ρ ^ n := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC fun k => ?_
    have hr1 : (‖a‖ / ρ) ^ k ≤ 1 := pow_le_one₀ hr0 hr.le
    calc ‖PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k‖
        ≤ M / ρ ^ n * (‖a‖ / ρ) ^ k := norm_shift_term_le F hρ hF a ha n k
      _ ≤ M / ρ ^ n * 1 := by gcongr
      _ = M / ρ ^ n := mul_one _
  exact (le_div_iff₀ (pow_pos hρ n)).mp h

private theorem tsum_prod_eq_tsum_sum_antidiagonal (T : ℕ × ℕ → L) (hT : Summable T) :
    ∑' p : ℕ × ℕ, T p = ∑' N : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal N, T p := by
  have h1 : Summable (fun c : (Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n) =>
      T (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd c)) :=
    (Equiv.summable_iff _).mpr hT
  rw [← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd).tsum_eq T,
    h1.tsum_sigma' (fun N => (hasSum_fintype _).summable)]
  refine tsum_congr fun N => ?_
  rw [← Finset.tsum_subtype (Finset.HasAntidiagonal.antidiagonal N) T]
  rfl

private theorem tsum_coeff_taylorShift_mul_pow_eq (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (a : L) (ha : ‖a‖ < ρ)
    (b : L) (hb : ‖b‖ < ρ) :
    ∑' n, PowerSeries.coeff n (PowerSeries.mk fun n => ∑' k : ℕ,
        PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k) * b ^ n
      = ∑' n, PowerSeries.coeff n F * (a + b) ^ n := by
  set T : ℕ × ℕ → L := fun p =>
    PowerSeries.coeff (p.1 + p.2) F * ((p.1 + p.2).choose p.1 : L) * a ^ p.2 * b ^ p.1 with hT
  have hra : ‖a‖ / ρ < 1 := (div_lt_one hρ).mpr ha
  have hra0 : 0 ≤ ‖a‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  have hrb : ‖b‖ / ρ < 1 := (div_lt_one hρ).mpr hb
  have hrb0 : 0 ≤ ‖b‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  have hdom : ∀ p : ℕ × ℕ, ‖T p‖ ≤ M * ((‖b‖ / ρ) ^ p.1 * (‖a‖ / ρ) ^ p.2) := by
    rintro ⟨n, k⟩
    simp only [hT]
    rw [norm_mul, norm_pow]
    have h1 := norm_shift_term_le F hρ hF a ha n k
    calc ‖PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k‖ * ‖b‖ ^ n
        ≤ M / ρ ^ n * (‖a‖ / ρ) ^ k * ‖b‖ ^ n := by gcongr
      _ = M * ((‖b‖ / ρ) ^ n * (‖a‖ / ρ) ^ k) := by simp only [div_pow]; field_simp
  have hsum : Summable T := by
    refine Summable.of_norm_bounded ?_ hdom
    exact ((summable_geometric_of_lt_one hrb0 hrb).mul_of_nonneg
      (summable_geometric_of_lt_one hra0 hra)
      (fun _ => pow_nonneg hrb0 _) (fun _ => pow_nonneg hra0 _)).mul_left M
  have hLHS : ∑' n, PowerSeries.coeff n (PowerSeries.mk fun n => ∑' k : ℕ,
        PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k) * b ^ n
      = ∑' p : ℕ × ℕ, T p := by
    rw [hsum.tsum_prod' (fun n => hsum.prod_factor n)]
    refine tsum_congr fun n => ?_
    rw [PowerSeries.coeff_mk, ← tsum_mul_right]
  have hRHS : ∑' N, PowerSeries.coeff N F * (a + b) ^ N = ∑' p : ℕ × ℕ, T p := by
    rw [tsum_prod_eq_tsum_sum_antidiagonal T hsum]
    refine tsum_congr fun N => ?_
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, add_comm a b, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    simp only [hT]
    rw [show m + (N - m) = N by omega]
    ring
  rw [hLHS, hRHS]

private theorem tsum_eq_pow_mul_tsum_of_forall_lt (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (z : L) (hz : ‖z‖ < ρ)
    (n₀ : ℕ) (h0 : ∀ n < n₀, PowerSeries.coeff n F = 0) :
    ∑' n, PowerSeries.coeff n F * z ^ n
      = z ^ n₀ * ∑' m : ℕ, PowerSeries.coeff (n₀ + m) F * z ^ m := by
  have hs := (summable_and_norm_tsum_coeff_mul_pow_le F hρ hF z hz).1
  rw [← hs.sum_add_tsum_nat_add n₀, Finset.sum_eq_zero (fun n hn => by
      rw [Finset.mem_range] at hn
      rw [h0 n hn, zero_mul]), zero_add, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [add_comm m n₀, pow_add]
  ring

private theorem eq_zero_of_forall_tsum_coeff_mul_pow_eq_zero
    (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (h : ∀ z : L, ‖z‖ < ρ → ∑' n, PowerSeries.coeff n F * z ^ n = 0) : F = 0 := by
  by_contra hne
  set n₀ : ℕ := F.order.toNat with hn₀
  have hn₀' : F.order = n₀ := (PowerSeries.coe_toNat_order hne).symm
  have hc : PowerSeries.coeff n₀ F ≠ 0 := PowerSeries.coeff_order hne
  have hlt : ∀ n < n₀, PowerSeries.coeff n F = 0 := fun n hn =>
    PowerSeries.coeff_of_lt_order n (by rw [hn₀']; exact_mod_cast hn)
  have hM := bound_nonneg F hF
  obtain ⟨z, hz0, hzlt⟩ := NormedField.exists_norm_lt L
    (lt_min hρ (div_pos (mul_pos (norm_pos_iff.mpr hc) (pow_pos hρ (n₀ + 1)))
      (by linarith : (0 : ℝ) < M + 1)))
  have hzρ : ‖z‖ < ρ := lt_of_lt_of_le hzlt (min_le_left _ _)
  have hzc : ‖z‖ < ‖PowerSeries.coeff n₀ F‖ * ρ ^ (n₀ + 1) / (M + 1) :=
    lt_of_lt_of_le hzlt (min_le_right _ _)
  have hev := h z hzρ
  rw [tsum_eq_pow_mul_tsum_of_forall_lt F hρ hF z hzρ n₀ hlt] at hev
  have hz0' : z ≠ 0 := norm_pos_iff.mp hz0
  have hE : ∑' m : ℕ, PowerSeries.coeff (n₀ + m) F * z ^ m = 0 :=
    (mul_eq_zero.mp hev).resolve_left (pow_ne_zero _ hz0')
  have hs := summable_shifted F hρ hF z hzρ n₀
  rw [hs.tsum_eq_zero_add] at hE
  simp only [add_zero, pow_zero, mul_one] at hE
  have hE1 : ‖∑' m : ℕ, PowerSeries.coeff (n₀ + (m + 1)) F * z ^ (m + 1)‖
      ≤ ‖z‖ * (M / ρ ^ (n₀ + 1)) := by
    have heq : ∑' m : ℕ, PowerSeries.coeff (n₀ + (m + 1)) F * z ^ (m + 1)
        = z * ∑' m : ℕ, PowerSeries.coeff (n₀ + 1 + m) F * z ^ m := by
      rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      rw [show n₀ + (m + 1) = n₀ + 1 + m by omega, pow_succ]
      ring
    rw [heq, norm_mul]
    gcongr
    exact norm_tsum_shifted_le F hρ hF z hzρ (n₀ + 1)
  have heq2 : PowerSeries.coeff n₀ F
      = -∑' m : ℕ, PowerSeries.coeff (n₀ + (m + 1)) F * z ^ (m + 1) :=
    eq_neg_of_add_eq_zero_left hE
  have hnorm : ‖PowerSeries.coeff n₀ F‖ ≤ ‖z‖ * (M / ρ ^ (n₀ + 1)) := by
    rw [heq2, norm_neg]
    exact hE1
  have hρn : 0 < ρ ^ (n₀ + 1) := pow_pos hρ _
  have h3 : ‖z‖ * (M / ρ ^ (n₀ + 1)) < ‖PowerSeries.coeff n₀ F‖ := by
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < M + 1)] at hzc
    rw [mul_div_assoc', div_lt_iff₀ hρn]
    nlinarith [norm_nonneg z, norm_nonneg (PowerSeries.coeff n₀ F)]
  linarith

private theorem eq_of_forall_tsum_coeff_mul_pow_eq (F G : PowerSeries L) {ρ M M' : ℝ}
    (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M')
    (h : ∀ z : L, ‖z‖ < ρ →
      ∑' n, PowerSeries.coeff n F * z ^ n = ∑' n, PowerSeries.coeff n G * z ^ n) :
    F = G := by
  have hFG : ∀ n, ‖PowerSeries.coeff n (F - G)‖ * ρ ^ n ≤ max M M' := by
    intro n
    rw [map_sub]
    have hρn : 0 ≤ ρ ^ n := (pow_pos hρ n).le
    calc ‖PowerSeries.coeff n F - PowerSeries.coeff n G‖ * ρ ^ n
        ≤ max ‖PowerSeries.coeff n F‖ ‖PowerSeries.coeff n G‖ * ρ ^ n := by
          gcongr
          calc ‖PowerSeries.coeff n F - PowerSeries.coeff n G‖
              = ‖PowerSeries.coeff n F + -PowerSeries.coeff n G‖ := by rw [sub_eq_add_neg]
            _ ≤ max ‖PowerSeries.coeff n F‖ ‖-PowerSeries.coeff n G‖ :=
                IsUltrametricDist.norm_add_le_max _ _
            _ = max ‖PowerSeries.coeff n F‖ ‖PowerSeries.coeff n G‖ := by rw [norm_neg]
      _ = max (‖PowerSeries.coeff n F‖ * ρ ^ n) (‖PowerSeries.coeff n G‖ * ρ ^ n) :=
          (max_mul_of_nonneg _ _ hρn)
      _ ≤ max M M' := max_le_max (hF n) (hG n)
  have h0 := eq_zero_of_forall_tsum_coeff_mul_pow_eq_zero (F - G) hρ hFG (fun z hz => by
    have hs1 := (summable_and_norm_tsum_coeff_mul_pow_le F hρ hF z hz).1
    have hs2 := (summable_and_norm_tsum_coeff_mul_pow_le G hρ hG z hz).1
    simp only [map_sub, sub_mul]
    rw [hs1.tsum_sub hs2, h z hz, sub_self])
  exact sub_eq_zero.mp h0

/-- The Taylor shift of a power series by `a`: the coefficient of degree
`n` is the (conditionally convergent, in general) sum
`∑' k, coeff (n + k) F * (n + k).choose n * a ^ k`. Under a coefficient
bound `‖coeff n F‖ * ρ ^ n ≤ M` with `‖a‖ < ρ` in a complete
nonarchimedean field, each sum converges; see
`summable_taylorShift_coeff`. -/
public noncomputable def taylorShift (a : L) (F : PowerSeries L) :
    PowerSeries L :=
  PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) F
    * ((n + k).choose n : L) * a ^ k

/-- Coefficients of a Taylor shift, by definition. -/
public theorem coeff_taylorShift (a : L) (F : PowerSeries L) (n : ℕ) :
    PowerSeries.coeff n (taylorShift a F)
      = ∑' k : ℕ, PowerSeries.coeff (n + k) F
        * ((n + k).choose n : L) * a ^ k :=
  PowerSeries.coeff_mk _ _

/-- Under a coefficient bound inside radius `ρ`, the defining sum of
each Taylor-shift coefficient converges. -/
public theorem summable_taylorShift_coeff (F : PowerSeries L) {ρ M : ℝ}
    (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (a : L) (ha : ‖a‖ < ρ) (n : ℕ) :
    Summable (fun k : ℕ => PowerSeries.coeff (n + k) F
      * ((n + k).choose n : L) * a ^ k) :=
  (norm_coeff_taylorShift_mul_pow_le F hρ hF a ha n).1

/-- The Taylor shift inherits the same coefficient bound at radius
`ρ`. -/
public theorem norm_coeff_taylorShift_mul_pow_le' (F : PowerSeries L)
    {ρ M : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (a : L)
    (ha : ‖a‖ < ρ) (n : ℕ) :
    ‖PowerSeries.coeff n (taylorShift a F)‖ * ρ ^ n ≤ M :=
  (norm_coeff_taylorShift_mul_pow_le F hρ hF a ha n).2

/-- Multiplicativity of the convergent nonarchimedean Taylor shift: shifting
a product of two power series by `a` inside a common coefficient-bound
radius is the product of the shifts. -/
public theorem taylorShift_mul (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M') (a : L) (ha : ‖a‖ < ρ) :
    taylorShift a (F * G) = taylorShift a F * taylorShift a G := by
  show (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) (F * G)
        * ((n + k).choose n : L) * a ^ k)
      = (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) F
          * ((n + k).choose n : L) * a ^ k)
        * (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) G
          * ((n + k).choose n : L) * a ^ k)
  have hFG : ∀ n, ‖PowerSeries.coeff n (F * G)‖ * ρ ^ n ≤ M * M' :=
    norm_coeff_mul_mul_pow_le F G hρ.le hF hG
  have hSFG := fun n => (norm_coeff_taylorShift_mul_pow_le (F * G) hρ hFG a ha n).2
  have hSF := fun n => (norm_coeff_taylorShift_mul_pow_le F hρ hF a ha n).2
  have hSG := fun n => (norm_coeff_taylorShift_mul_pow_le G hρ hG a ha n).2
  have hprod := norm_coeff_mul_mul_pow_le _ _ hρ.le hSF hSG
  refine eq_of_forall_tsum_coeff_mul_pow_eq _ _ hρ hSFG hprod (fun b hb => ?_)
  rw [tsum_coeff_mul_mul_pow_eq_of_norm_lt _ _ hρ hSF hSG b hb,
    tsum_coeff_taylorShift_mul_pow_eq (F * G) hρ hFG a ha b hb,
    tsum_coeff_taylorShift_mul_pow_eq F hρ hF a ha b hb,
    tsum_coeff_taylorShift_mul_pow_eq G hρ hG a ha b hb]
  have hab : ‖a + b‖ < ρ := lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)
  exact tsum_coeff_mul_mul_pow_eq_of_norm_lt F G hρ hF hG (a + b) hab

end PowerSeries
