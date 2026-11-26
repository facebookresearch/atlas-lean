/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Bounds in Luca's generalized Fibonacci discriminant equation

We compare the recurrence directly with geometric sequences instead of using
its characteristic roots. The lower comparison uses the base `2 * (1 - 1 / 2^k)`.
-/

namespace MetaMathlibExt

open scoped BigOperators

section Recurrence

variable {k : ℕ} {F : ℤ → ℤ}
variable (hFzero : ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n < 1 → F n = 0)
variable (hFone : F 1 = 1)
variable (hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range k, F (n - 1 - (i : ℤ)))

include hFzero hFone hFrec in
private lemma recurrence_nonneg (hk : 2 ≤ k) (n : ℕ) : 0 ≤ F n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : 1 < n
    · rw [hFrec _ (by exact_mod_cast hn)]
      apply Finset.sum_nonneg
      intro i hi
      have hik := Finset.mem_range.mp hi
      let t : ℤ := (n : ℤ) - 1 - (i : ℤ)
      change 0 ≤ F t
      by_cases ht : t < 1
      · rw [hFzero t (by dsimp [t]; omega) ht]
      · rw [← Int.toNat_of_nonneg (show 0 ≤ t by omega)]
        exact ih t.toNat (by dsimp [t]; omega)
    · have h : n = 0 ∨ n = 1 := by omega
      rcases h with rfl | rfl
      · simp [hFzero 0 (by omega) (by decide)]
      · simp [hFone]

-- Subtract successive copies of the recurrence; only the two end terms differ.
include hFrec in
private lemma recurrence_step (hk : 2 ≤ k) {t : ℤ} (ht : 1 < t) :
    F (t + 1) + F (t - (k : ℤ)) = 2 * F t := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  have hnext := hFrec (t + 1) (by omega)
  rw [Finset.sum_range_succ'] at hnext
  have hnow := hFrec t ht
  rw [Finset.sum_range_succ] at hnow
  push_cast at hnext hnow ⊢
  simp only [sub_zero, add_sub_cancel_right] at hnext
  have hshift (i : ℕ) : t - ((i : ℤ) + 1) = t - 1 - (i : ℤ) := by omega
  simp only [hshift] at hnext
  have hend : t - 1 - (j : ℤ) = t - ((j : ℤ) + 1) := by omega
  rw [hend] at hnow
  linarith

include hFzero hFone hFrec in
private lemma recurrence_initial (hk : 2 ≤ k) (m : ℕ) (hm : m + 1 ≤ k) :
    F (m + 2 : ℤ) = 2 ^ m := by
  induction m with
  | zero =>
    norm_num only [Nat.cast_zero, zero_add, pow_zero]
    rw [hFrec 2 (by decide), Finset.sum_eq_single 0]
    · simpa using hFone
    · intro i hi hi0
      have hik := Finset.mem_range.mp hi
      apply hFzero <;> omega
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  | succ m ih =>
    have hs := recurrence_step hFrec hk (t := (m : ℤ) + 2) (by omega)
    rw [hFzero ((m : ℤ) + 2 - (k : ℤ)) (by omega) (by omega), add_zero,
      ih (by omega)] at hs
    push_cast
    rw [show (m : ℤ) + 1 + 2 = (m : ℤ) + 2 + 1 by omega, hs, pow_succ, mul_comm]

include hFzero hFone hFrec in
private lemma recurrence_le_pow (hk : 2 ≤ k) (m : ℕ) : F (m + 1 : ℤ) ≤ 2 ^ m := by
  induction m with
  | zero => simp [hFone]
  | succ m ih =>
    by_cases hm : m = 0
    · subst m
      have h := recurrence_initial hFzero hFone hFrec hk 0 (by omega)
      norm_num at h ⊢
      omega
    have hs := recurrence_step hFrec hk (t := (m : ℤ) + 1) (by omega)
    let t : ℤ := (m : ℤ) + 1 - (k : ℤ)
    have ht : 0 ≤ F t := by
      by_cases ht : t < 1
      · rw [hFzero _ (by dsimp [t]; omega) ht]
      · rw [← Int.toNat_of_nonneg (show 0 ≤ t by omega)]
        exact recurrence_nonneg hFzero hFone hFrec hk t.toNat
    push_cast
    rw [pow_succ]
    change F ((m : ℤ) + 1 + 1) ≤ 2 ^ m * 2
    change 0 ≤ F ((m : ℤ) + 1 - (k : ℤ)) at ht
    linarith

-- Once the whole window lies above index 1, the geometric sequence is a subsolution.
include hFzero hFone hFrec in
private lemma pow_le_recurrence (hk : 2 ≤ k) {a : ℝ} (ha : 0 ≤ a) (ha₂ : a ≤ 2)
    (hgeom : a ^ k ≤ ∑ i ∈ Finset.range k, a ^ i) (m : ℕ) :
    a ^ m ≤ (F (m + 2 : ℤ) : ℝ) := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    by_cases hm : m < k
    · rw [recurrence_initial hFzero hFone hFrec hk m (by omega)]
      push_cast
      exact pow_le_pow_left₀ ha ha₂ m
    · let r := m - k
      have hr : r + k = m := by dsimp [r]; omega
      have hrec : (F (m + 2 : ℤ) : ℝ) = ∑ i ∈ Finset.range k, (F (r + i + 2 : ℤ) : ℝ) := by
        rw [hFrec _ (by omega), Int.cast_sum,
          ← Finset.sum_range_reflect (fun i : ℕ => (F (r + i + 2 : ℤ) : ℝ)) k]
        apply Finset.sum_congr rfl
        intro i hi
        have hik := Finset.mem_range.mp hi
        congr 2
        omega
      calc
        a ^ m = a ^ r * a ^ k := by rw [← pow_add, hr]
        _ ≤ a ^ r * ∑ i ∈ Finset.range k, a ^ i :=
          mul_le_mul_of_nonneg_left hgeom (pow_nonneg ha _)
        _ = ∑ i ∈ Finset.range k, a ^ (r + i) := by simp only [Finset.mul_sum, pow_add]
        _ ≤ (F (m + 2 : ℤ) : ℝ) := by
          rw [hrec]
          apply Finset.sum_le_sum
          intro i hi
          have hik := Finset.mem_range.mp hi
          simpa only [Nat.cast_add] using ih (r + i) (by omega)

end Recurrence

-- One dyadic estimate suffices for both logarithmic errors.
private lemma dyadic_bound {k : ℕ} (hk : 100 < k) : 10000 * ((k : ℝ) + 1) ^ 2 < (2 : ℝ) ^ k := by
  have hk' : 101 ≤ k := by omega
  clear hk
  induction k, hk' using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hkR : (101 : ℝ) ≤ k := by exact_mod_cast hk
    rw [Nat.cast_succ, pow_succ (2 : ℝ) k]
    have hs : ((k : ℝ) + 1 + 1) ^ 2 ≤ 2 * ((k : ℝ) + 1) ^ 2 := by
      nlinarith [sq_nonneg (k : ℝ)]
    linarith only [hs, ih]

-- Bernoulli's inequality gives `(2 - a) * a^k ≥ 1`, the geometric comparison condition.
private lemma comparison_geom (k : ℕ) {D : ℝ} (hD : D = (2 : ℝ) ^ k) (hDpos : 0 < D)
    (hx₀ : 1 / D ≤ 1 / 2) (hx : (k : ℝ) / D ≤ 1 / 2)
    {a : ℝ} (ha : a = 2 * (1 - 1 / D)) (ha₁ : 1 < a) :
    a ^ k ≤ ∑ i ∈ Finset.range k, a ^ i := by
  have hb := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ 1 - 1 / D by linarith) k
  have hb' : (1 / 2 : ℝ) ≤ (1 - 1 / D) ^ k := by
    calc
      (1 / 2 : ℝ) ≤ 1 - (k : ℝ) / D := by linarith
      _ = 1 + (k : ℝ) * (1 - 1 / D - 1) := by ring
      _ ≤ _ := hb
  have hc : 1 ≤ (2 - a) * a ^ k := by
    rw [show 2 - a = 2 / D by rw [ha]; ring, ha, mul_pow, ← hD]
    rw [← mul_assoc, div_mul_cancel₀ _ hDpos.ne']
    linarith
  apply le_of_mul_le_mul_right _ (sub_pos.mpr ha₁)
  rw [geom_sum_mul]
  linarith

private lemma neg_two_mul_le_log_one_sub {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    -2 * x ≤ Real.log (1 - x) := by
  have hp : 0 < 1 - x := by linarith
  calc
    -2 * x ≤ 1 - (1 - x)⁻¹ := by
      rw [inv_eq_one_div, le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le,
        div_le_iff₀ hp]
      nlinarith [mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith)]
    _ ≤ _ := Real.one_sub_inv_le_log_of_pos hp

private lemma correction_lt (k : ℕ) (hk : 0 < k) :
    ((k : ℝ) + 1) ^ (k + 1) / ((2 : ℝ) ^ (k + 1) * (k : ℝ) ^ k) <
      4 * ((k : ℝ) + 1) / (2 : ℝ) ^ (k + 1) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hexp : (1 + (k : ℝ)⁻¹) ^ k < 4 :=
    Real.one_add_inv_pow_le_exp.trans_lt (Real.exp_one_lt_three.trans (by norm_num))
  have heq : (k : ℝ) + 1 = (1 + (k : ℝ)⁻¹) * (k : ℝ) := by
    rw [add_mul, one_mul, inv_mul_cancel₀ hkR.ne']
  have hpow : ((k : ℝ) + 1) ^ k < 4 * (k : ℝ) ^ k := by
    conv_lhs => rw [heq, mul_pow]
    exact mul_lt_mul_of_pos_right hexp (pow_pos hkR _)
  rw [pow_succ ((k : ℝ) + 1), ← div_div]
  rw [div_right_comm]
  apply div_lt_div_of_pos_right _ (by positivity)
  rw [div_lt_iff₀ (pow_pos hkR _)]
  calc
    ((k : ℝ) + 1) ^ k * ((k : ℝ) + 1) < (4 * (k : ℝ) ^ k) * ((k : ℝ) + 1) :=
      mul_lt_mul_of_pos_right hpow (by positivity)
    _ = _ := by ring

/-- **Bounds on the index in Luca's discriminant equation.** Let $k > 100$ be a natural number
and let $F : \mathbb{Z} \to \mathbb{Z}$ satisfy $F(n) = 0$ for every integer $n$ with
$2 - k \le n \le 0$, $F(1) = 1$, and $F(n) = F(n-1) + F(n-2) + \cdots + F(n-k)$ for every
integer $n \ge 2$ (the $k$-generalized Fibonacci sequence). Write
$L = (k \log k - 2 \log(k-1)) / \log 2$, where $\log$ is the natural logarithm. If a natural
number $n$ satisfies $F(n)\,(k-1)^2 = 2^{k+1} k^k - (k+1)^{k+1}$, then
$k + 1.99 + L < n < k + 3.01 + L$.

The equation is the paper's equation (7),
$F(n) = (2^{k+1} k^k - (k+1)^{k+1}) / (k-1)^2$, multiplied by $(k-1)^2$.

Source: Florian Luca, *On the Discriminant of the k-Generalized Fibonacci Polynomial, II*,
The Fibonacci Quarterly 62 (2024), no. 3, Lemma 1 (`fq-2024-luca02082024-lem-1`). Equation (7) is
written after
multiplying by `(k-1)^2`; `F^{(k)}` is given by its defining properties as in
`abs_discr_kGeneralizedFibonacciPolynomial_mem_iff`. By Theorem 1 the equation has no
solution with `k > 100`, so this intermediate bound is implied by that statement. -/
public theorem kGeneralizedFibonacci_discr_eq_index_bounds (k : ℕ) (hk : 100 < k)
    (F : ℤ → ℤ) (hFzero : ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n < 1 → F n = 0) (hFone : F 1 = 1)
    (hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range k, F (n - 1 - (i : ℤ)))
    (n : ℕ)
    (h7 : F n * ((k : ℤ) - 1) ^ 2 = 2 ^ (k + 1) * (k : ℤ) ^ k - ((k : ℤ) + 1) ^ (k + 1)) :
    (k : ℝ) + 1.99 + ((k : ℝ) * Real.log k - 2 * Real.log ((k : ℝ) - 1)) / Real.log 2 <
        (n : ℝ) ∧
      (n : ℝ) < (k : ℝ) + 3.01 +
        ((k : ℝ) * Real.log k - 2 * Real.log ((k : ℝ) - 1)) / Real.log 2 := by
  have hk₂ : 2 ≤ k := by omega
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk₂
  have hkpos : (0 : ℝ) < k := by positivity
  have hpred : 0 < (k : ℝ) - 1 := by linarith
  set D : ℝ := 2 ^ k with hD
  have hDpos : 0 < D := by positivity
  have hdy : 10000 * ((k : ℝ) + 1) ^ 2 < D := dyadic_bound hk
  have hx : 1 / D ≤ (1 / 8 : ℝ) := (div_le_iff₀ hDpos).mpr (by nlinarith)
  have hkx : (k : ℝ) / D ≤ 1 / 2 := (div_le_iff₀ hDpos).mpr (by nlinarith)
  set a : ℝ := 2 * (1 - 1 / D) with ha
  have ha₁ : 1 < a := by rw [ha]; linarith
  have hapos : 0 < a := by linarith
  have ha₂ : a ≤ 2 := by rw [ha]; linarith [div_pos one_pos hDpos]
  have hgeom := comparison_geom k hD hDpos (hx.trans (by norm_num)) hkx ha ha₁
  set N : ℝ := (2 : ℝ) ^ (k + 1) * (k : ℝ) ^ k with hN
  let c : ℝ := ((k : ℝ) + 1) ^ (k + 1) / N
  set A : ℝ := N / ((k : ℝ) - 1) ^ 2 with hA
  have hNpos : 0 < N := by positivity
  have hApos : 0 < A := by positivity
  have hcpos : 0 < c := by positivity
  -- The factor `k + 1` in the correction is retained; it is still small enough.
  have hc_lt : c < 1 / 400 := by
    calc
      c < 4 * ((k : ℝ) + 1) / (2 : ℝ) ^ (k + 1) := correction_lt k (by omega)
      _ = 2 * ((k : ℝ) + 1) / D := by rw [pow_succ, ← hD]; ring
      _ < _ := (div_lt_iff₀ hDpos).mpr (by nlinarith)
  have h7R : (F n : ℝ) * ((k : ℝ) - 1) ^ 2 = N - ((k : ℝ) + 1) ^ (k + 1) := by
    dsimp only [N]
    exact_mod_cast h7
  have hF : (F n : ℝ) = A * (1 - c) := by
    calc
      (F n : ℝ) = (N - ((k : ℝ) + 1) ^ (k + 1)) / ((k : ℝ) - 1) ^ 2 :=
        (eq_div_iff (pow_ne_zero _ hpred.ne')).mpr h7R
      _ = A * (1 - c) := by
        dsimp only [A, c]
        field_simp [hNpos.ne']
  have hA8 : 8 ≤ A := by
    have hden_le : ((k : ℝ) - 1) ^ 2 ≤ (k : ℝ) ^ k :=
      (pow_le_pow_left₀ hpred.le (by linarith) 2).trans
        (pow_le_pow_right₀ (by linarith) hk₂)
    have h8 : (8 : ℝ) ≤ 2 ^ (k + 1) := by
      calc
        (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
        _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [hA, hN, mul_div_assoc]
    exact h8.trans (le_mul_of_one_le_right (by positivity)
      ((one_le_div (by positivity)).mpr hden_le))
  have hFgt : 1 < (F n : ℝ) := by
    rw [hF]
    calc
      (1 : ℝ) < 8 * (1 / 2) := by norm_num
      _ ≤ A * (1 - c) := mul_le_mul hA8 (by linarith) (by norm_num) hApos.le
  have hn : 2 ≤ n := by
    by_contra! h
    have he : n = 0 ∨ n = 1 := by omega
    rcases he with rfl | rfl
    · have hz := hFzero 0 (by omega) (by decide)
      norm_num [hz] at hFgt
    · norm_num [hFone] at hFgt
  have hlow : a ^ (n - 2) ≤ (F n : ℝ) := by
    have he : ((n - 2 : ℕ) : ℤ) + 2 = n := by omega
    simpa only [he] using pow_le_recurrence hFzero hFone hFrec hk₂ hapos.le ha₂ hgeom (n - 2)
  have hupp : (F n : ℝ) ≤ 2 ^ (n - 1) := by
    have he : ((n - 1 : ℕ) : ℤ) + 1 = n := by omega
    exact_mod_cast he ▸ recurrence_le_pow hFzero hFone hFrec hk₂ (n - 1)
  have hFlt : (F n : ℝ) < A := by
    rw [hF]
    exact mul_lt_of_lt_one_right hApos (by linarith)
  have hlog₂lo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    calc
      (1 / 2 : ℝ) = 1 - (2 : ℝ)⁻¹ := by norm_num
      _ ≤ _ := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hlog₂hi : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hlog₂pos : 0 < Real.log 2 := by linarith
  have hlogA : Real.log A = ((k : ℝ) + 1) * Real.log 2 +
      (k : ℝ) * Real.log k - 2 * Real.log ((k : ℝ) - 1) := by
    rw [hA, hN, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    norm_num
  have hdiv : (2 : ℝ) / D = 2 * (1 / D) := by ring
  have hlog_a : Real.log 2 - 2 / D ≤ Real.log a := by
    rw [ha, Real.log_mul (by norm_num) (by linarith)]
    linarith only [hdiv, neg_two_mul_le_log_one_sub (div_nonneg zero_le_one hDpos.le)
      (hx.trans (by norm_num))]
  have hlog_low := Real.log_lt_log (pow_pos hapos (n - 2)) (hlow.trans_lt hFlt)
  rw [Real.log_pow, Nat.cast_sub hn, Nat.cast_ofNat] at hlog_low
  have hlog_upp := Real.log_le_log (zero_lt_one.trans hFgt) hupp
  rw [hF, Real.log_mul hApos.ne' (by linarith), Real.log_pow,
    Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one] at hlog_upp
  -- On the lower side, take logs of the normalized equation and use the small correction.
  have herr_lo : -(0.01 : ℝ) * Real.log 2 < Real.log (1 - c) := by
    linarith only [hc_lt, hlog₂lo, neg_two_mul_le_log_one_sub hcpos.le (by linarith only [hc_lt])]
  -- On the upper side, first bound the index coarsely, then bound the loss from `log a`.
  have hlogA_le : Real.log A ≤ ((k : ℝ) + 1) ^ 2 := by
    have hlogk := Real.log_le_sub_one_of_pos hkpos
    have hlogpred : 0 ≤ Real.log ((k : ℝ) - 1) := Real.log_nonneg (by linarith)
    rw [hlogA]
    nlinarith only [mul_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity) (sub_nonneg.mpr hlog₂hi),
      mul_nonneg hkpos.le (sub_nonneg.mpr hlogk), hlogpred]
  have hnR : (0 : ℝ) ≤ n - 2 := sub_nonneg.mpr (by exact_mod_cast hn)
  have hlog_a_lo : (1 / 4 : ℝ) ≤ Real.log a := by linarith only [hdiv, hx, hlog₂lo, hlog_a]
  have hcoarse : (n : ℝ) - 2 < 4 * ((k : ℝ) + 1) ^ 2 := by
    nlinarith only [mul_nonneg hnR (sub_nonneg.mpr hlog_a_lo), hlog_low, hlogA_le]
  have herr_hi : ((n : ℝ) - 2) * (2 / D) < (0.01 : ℝ) * Real.log 2 := by
    calc
      ((n : ℝ) - 2) * (2 / D) = (((n : ℝ) - 2) * 2) / D := by ring
      _ < 1 / 200 := (div_lt_iff₀ hDpos).mpr (by nlinarith only [hcoarse, hdy])
      _ ≤ _ := by linarith only [hlog₂lo]
  have hu : ((n : ℝ) - 2) * Real.log 2 < Real.log A + (0.01 : ℝ) * Real.log 2 := by
    nlinarith only [mul_nonneg hnR (sub_nonneg.mpr hlog_a), hlog_low, herr_hi]
  constructor
  · have h : ((k : ℝ) * Real.log k - 2 * Real.log ((k : ℝ) - 1)) / Real.log 2 <
        (n : ℝ) - ((k : ℝ) + 1.99) := (div_lt_iff₀ hlog₂pos).mpr (by
      linarith only [hlogA, hlog_upp, herr_lo])
    linarith only [h]
  · have h : (n : ℝ) - ((k : ℝ) + 3.01) <
        ((k : ℝ) * Real.log k - 2 * Real.log ((k : ℝ) - 1)) / Real.log 2 :=
      (lt_div_iff₀ hlog₂pos).mpr (by linarith only [hlogA, hu])
    linarith only [h]

end MetaMathlibExt
