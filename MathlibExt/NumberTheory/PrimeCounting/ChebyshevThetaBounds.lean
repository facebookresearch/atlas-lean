/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.Floor.Semifield

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.MeanInequalities
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Misc

@[expose] public section

open Nat hiding log
open Finset Real
open ArithmeticFunction hiding log id

/-- Chebyshev's 30-weight constant. -/
private noncomputable def ctbA0 : ℝ :=
  (1 / 2) * Real.log 2 + (1 / 3) * Real.log 3 + (1 / 5) * Real.log 5 -
    (1 / 30) * Real.log 30

/-- Chebyshev's combination weight `m - m/2 - m/3 - m/5 + m/30` (ℕ-division). -/
private def ctbW (m : ℕ) : ℤ :=
  (m : ℤ) - ((m / 2 : ℕ) : ℤ) - ((m / 3 : ℕ) : ℤ) - ((m / 5 : ℕ) : ℤ) +
    ((m / 30 : ℕ) : ℤ)

/-- Chebyshev's combination `U(N)` of log-factorials. -/
private noncomputable def ctbU (N : ℕ) : ℝ :=
  Real.log (N ! : ℝ) - Real.log ((N / 2)! : ℝ) - Real.log ((N / 3)! : ℝ) -
    Real.log ((N / 5)! : ℝ) + Real.log ((N / 30)! : ℝ)

/-- `log (N!)` as a von Mangoldt sum. -/
private theorem ctb_log_fact (N : ℕ) : Real.log (N ! : ℝ) =
    ∑ n ∈ Finset.Ioc 0 N,
      ArithmeticFunction.vonMangoldt n * ((N / n : ℕ) : ℝ) := by
  have hsum : ∑ n ∈ Finset.Ioc 0 N, Real.log (n : ℝ) = Real.log (N ! : ℝ) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), ih, Nat.factorial_succ,
        Nat.cast_mul, Real.log_mul (by positivity) (by positivity),
        add_comm]
  rw [← hsum]
  have h : ∀ n : ℕ, Real.log (n : ℝ) =
      (ArithmeticFunction.vonMangoldt * ArithmeticFunction.zeta) n := by
    intro n
    rw [ArithmeticFunction.vonMangoldt_mul_zeta]
    exact (ArithmeticFunction.log_apply).symm
  simp_rw [h]
  exact ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum _ N

/-- The weight takes values in `{0, 1}`, and equals `1` on `[1, 6)`. -/
private theorem ctbW_nonneg (m : ℕ) : 0 ≤ ctbW m := by
  unfold ctbW
  omega

private theorem ctbW_le_one (m : ℕ) : ctbW m ≤ 1 := by
  unfold ctbW
  omega

private theorem ctbW_eq_one (m : ℕ) (h1 : 1 ≤ m) (h6 : m < 6) :
    ctbW m = 1 := by
  unfold ctbW
  omega

/-- Helper: rescale a von Mangoldt sum from `N / d` to `N`. -/
private theorem ctb_rescale (N d : ℕ) (hd : 0 < d) :
    ∑ n ∈ Finset.Ioc 0 (N / d),
        ArithmeticFunction.vonMangoldt n * (((N / d) / n : ℕ) : ℝ) =
    ∑ n ∈ Finset.Ioc 0 N,
        ArithmeticFunction.vonMangoldt n * (((N / n) / d : ℕ) : ℝ) := by
  have hcongr : ∀ n ∈ Finset.Ioc 0 (N / d),
      ArithmeticFunction.vonMangoldt n * (((N / d) / n : ℕ) : ℝ) =
      ArithmeticFunction.vonMangoldt n * (((N / n) / d : ℕ) : ℝ) := by
    intro n _
    congr 1
    rw [Nat.div_div_eq_div_mul N d n, Nat.div_div_eq_div_mul N n d,
      mul_comm d n]
  rw [Finset.sum_congr rfl hcongr]
  apply Finset.sum_subset (Finset.Ioc_subset_Ioc_right (Nat.div_le_self N d))
  intro n hn hnot
  simp only [Finset.mem_Ioc, not_and] at hn hnot
  have hlt : N / d < n := lt_of_not_ge (fun h => hnot hn.1 h)
  have hNd : N / n < d := by
    rw [Nat.div_lt_iff_lt_mul hn.1]
    have hmod : N % d < d := Nat.mod_lt N hd
    have hle : N / d + 1 ≤ n := hlt
    calc N = d * (N / d) + N % d := (Nat.div_add_mod N d).symm
      _ < d * (N / d) + d := by omega
      _ = d * (N / d + 1) := by ring
      _ ≤ d * n := by gcongr
  simp [Nat.div_eq_of_lt hNd]

/-- `U(N)` as a weighted von Mangoldt sum. -/
private theorem ctbU_eq_sum (N : ℕ) : ctbU N =
    ∑ n ∈ Finset.Ioc 0 N,
      ArithmeticFunction.vonMangoldt n * ((ctbW (N / n) : ℤ) : ℝ) := by
  have e2 := ctb_rescale N 2 (by norm_num)
  have e3 := ctb_rescale N 3 (by norm_num)
  have e5 := ctb_rescale N 5 (by norm_num)
  have e30 := ctb_rescale N 30 (by norm_num)
  unfold ctbU
  rw [ctb_log_fact N, ctb_log_fact (N / 2), ctb_log_fact (N / 3),
    ctb_log_fact (N / 5), ctb_log_fact (N / 30), e2, e3, e5, e30,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have hc : ((ctbW (N / n) : ℤ) : ℝ) = ((N / n : ℕ) : ℝ) -
      ((((N / n) / 2 : ℕ)) : ℝ) - ((((N / n) / 3 : ℕ)) : ℝ) -
      ((((N / n) / 5 : ℕ)) : ℝ) + ((((N / n) / 30 : ℕ)) : ℝ) := by
    unfold ctbW
    simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast]
  rw [hc]
  ring

/-- Helper: `ψ` at a natural cast is the von Mangoldt sum. -/
private theorem ctb_psi_nat (N : ℕ) : Chebyshev.psi (N : ℝ) =
    ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n := by
  unfold Chebyshev.psi
  rw [Nat.floor_natCast]

/-- `ψ(N) - ψ(N/6) ≤ U(N) ≤ ψ(N)`. -/
private theorem ctb_sandwich_nat (N : ℕ) :
    Chebyshev.psi (N : ℝ) - Chebyshev.psi (((N / 6 : ℕ)) : ℝ) ≤ ctbU N ∧
    ctbU N ≤ Chebyshev.psi (N : ℝ) := by
  have hW : ∑ n ∈ Finset.Ioc 0 N,
        ArithmeticFunction.vonMangoldt n * ((ctbW (N / n) : ℤ) : ℝ) =
      (∑ n ∈ Finset.Ioc 0 (N / 6),
        ArithmeticFunction.vonMangoldt n * ((ctbW (N / n) : ℤ) : ℝ)) +
      (∑ n ∈ Finset.Ioc (N / 6) N,
        ArithmeticFunction.vonMangoldt n * ((ctbW (N / n) : ℤ) : ℝ)) :=
    (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.div_le_self N 6)).symm
  have hL : (∑ n ∈ Finset.Ioc 0 (N / 6), ArithmeticFunction.vonMangoldt n) +
      (∑ n ∈ Finset.Ioc (N / 6) N, ArithmeticFunction.vonMangoldt n) =
      ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n :=
    Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.div_le_self N 6)
  have h1 : (0 : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 (N / 6),
      ArithmeticFunction.vonMangoldt n * ((ctbW (N / n) : ℤ) : ℝ) :=
    Finset.sum_nonneg (fun n _ => mul_nonneg
      ArithmeticFunction.vonMangoldt_nonneg (by exact_mod_cast ctbW_nonneg _))
  have hterm : ∀ n ∈ Finset.Ioc (N / 6) N,
      ArithmeticFunction.vonMangoldt n * ((ctbW (N / n) : ℤ) : ℝ) =
      ArithmeticFunction.vonMangoldt n := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn.1
    have hNn1 : 1 ≤ N / n := (Nat.one_le_div_iff hn0).mpr hn.2
    have hNn6 : N / n < 6 := by
      rw [Nat.div_lt_iff_lt_mul hn0]
      have hmod : N % 6 < 6 := Nat.mod_lt N (by norm_num)
      have hle : N / 6 + 1 ≤ n := hn.1
      calc N = 6 * (N / 6) + N % 6 := (Nat.div_add_mod N 6).symm
        _ < 6 * (N / 6) + 6 := by omega
        _ = 6 * (N / 6 + 1) := by ring
        _ ≤ 6 * n := by gcongr
    rw [ctbW_eq_one _ hNn1 hNn6, Int.cast_one, mul_one]
  have h2 : ∑ n ∈ Finset.Ioc (N / 6) N,
      ArithmeticFunction.vonMangoldt n * ((ctbW (N / n) : ℤ) : ℝ) =
      (∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n) -
      (∑ n ∈ Finset.Ioc 0 (N / 6), ArithmeticFunction.vonMangoldt n) := by
    rw [Finset.sum_congr rfl hterm]
    linarith
  constructor
  · rw [ctbU_eq_sum, ctb_psi_nat N, ctb_psi_nat (N / 6), hW, h2]
    linarith
  · rw [ctbU_eq_sum, ctb_psi_nat N]
    apply Finset.sum_le_sum
    intro n _
    have hwR : ((ctbW (N / n) : ℤ) : ℝ) ≤ 1 := by
      exact_mod_cast ctbW_le_one _
    calc ArithmeticFunction.vonMangoldt n * ((ctbW (N / n) : ℤ) : ℝ)
        ≤ ArithmeticFunction.vonMangoldt n * 1 :=
          mul_le_mul_of_nonneg_left hwR
            ArithmeticFunction.vonMangoldt_nonneg
      _ = ArithmeticFunction.vonMangoldt n := mul_one _

/-- Real corollary. -/
private theorem ctb_sandwich_real (x : ℝ) :
    Chebyshev.psi x - Chebyshev.psi (x / 6) ≤ ctbU ⌊x⌋₊ ∧
    ctbU ⌊x⌋₊ ≤ Chebyshev.psi x := by
  have h6 : ⌊x / 6⌋₊ = ⌊x⌋₊ / 6 := by
    have hcast : (6 : ℝ) = ((6 : ℕ) : ℝ) := by norm_num
    rw [hcast, Nat.floor_div_natCast]
  have e1 : Chebyshev.psi x = Chebyshev.psi ((⌊x⌋₊ : ℕ) : ℝ) :=
    Chebyshev.psi_eq_psi_coe_floor x
  have e2 : Chebyshev.psi (x / 6) =
      Chebyshev.psi ((((⌊x⌋₊ / 6 : ℕ))) : ℝ) := by
    rw [Chebyshev.psi_eq_psi_coe_floor (x / 6), h6]
  rw [e1, e2]
  exact ctb_sandwich_nat ⌊x⌋₊

/-- Integer step: Stirling upper bound for `log (n!)`. -/
private theorem ctb_log_fact_int_upper (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n ! : ℝ) ≤
      (n : ℝ) * Real.log n - n + (1 / 2) * Real.log n + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hcast : ((k + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  have hanti : Stirling.stirlingSeq (k + 1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le k)
  have hpos : 0 < Stirling.stirlingSeq (k + 1) := Stirling.stirlingSeq'_pos k
  have hlog := Real.log_le_log hpos hanti
  rw [Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one] at hlog
  have e1 : Real.log (Real.exp 1 / Real.sqrt 2) = 1 - 1 / 2 * Real.log 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_exp,
      Real.log_sqrt (by norm_num)]
    ring
  have e2 : Real.log (2 * ((k + 1 : ℕ) : ℝ)) =
      Real.log 2 + Real.log ((k + 1 : ℕ) : ℝ) :=
    Real.log_mul (by norm_num) hcast
  have e4 : ((k + 1 : ℕ) : ℝ) *
      Real.log (((k + 1 : ℕ) : ℝ) / Real.exp 1) =
      ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) -
        ((k + 1 : ℕ) : ℝ) := by
    have e3 : Real.log (((k + 1 : ℕ) : ℝ) / Real.exp 1) =
        Real.log ((k + 1 : ℕ) : ℝ) - 1 := by
      rw [Real.log_div hcast (by positivity), Real.log_exp]
    rw [e3]
    ring
  rw [e1] at hlog
  linarith [hlog, e2, e4]

/-- Upper Stirling bound at real arguments. -/
private theorem ctb_log_fact_floor_upper (y : ℝ) (hy : 1 ≤ y) :
    Real.log ((⌊y⌋₊ ! : ℕ) : ℝ) ≤
      y * Real.log y - y + (1 / 2) * Real.log y + 1 := by
  have hn1 : 1 ≤ ⌊y⌋₊ := (Nat.one_le_floor_iff y).mpr hy
  have hle : ((⌊y⌋₊ : ℕ) : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hpos_n : (0 : ℝ) < ((⌊y⌋₊ : ℕ) : ℝ) := by
    have h0 : (0 : ℕ) < ⌊y⌋₊ := by omega
    exact_mod_cast h0
  have hpos_y : (0 : ℝ) < y := by linarith
  have hlog_le : Real.log ((⌊y⌋₊ : ℕ) : ℝ) ≤ Real.log y :=
    Real.log_le_log hpos_n hle
  have hint := ctb_log_fact_int_upper ⌊y⌋₊ hn1
  have hmul : y - ((⌊y⌋₊ : ℕ) : ℝ) ≤
      y * Real.log y - y * Real.log ((⌊y⌋₊ : ℕ) : ℝ) := by
    have hdiv : Real.log (y / ((⌊y⌋₊ : ℕ) : ℝ)) =
        Real.log y - Real.log ((⌊y⌋₊ : ℕ) : ℝ) :=
      Real.log_div (ne_of_gt hpos_y) (ne_of_gt hpos_n)
    have hbase := Real.one_sub_inv_le_log_of_pos
      (div_pos hpos_y hpos_n)
    rw [hdiv] at hbase
    have h := mul_le_mul_of_nonneg_left hbase (le_of_lt hpos_y)
    have hinv : y * (1 - (y / ((⌊y⌋₊ : ℕ) : ℝ))⁻¹) =
        y - ((⌊y⌋₊ : ℕ) : ℝ) := by
      have hy0 : y ≠ 0 := ne_of_gt hpos_y
      rw [inv_div, mul_sub, mul_one, ← mul_div_assoc,
        mul_div_cancel_left₀ _ hy0]
    rwa [hinv, mul_sub] at h
  have hgap : (0 : ℝ) ≤ y * Real.log ((⌊y⌋₊ : ℕ) : ℝ) -
      ((⌊y⌋₊ : ℕ) : ℝ) * Real.log ((⌊y⌋₊ : ℕ) : ℝ) := by
    have hnn : (0 : ℝ) ≤ Real.log ((⌊y⌋₊ : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hn1)
    have hprod := mul_nonneg (sub_nonneg.mpr hle) hnn
    have hbridge : (y - ((⌊y⌋₊ : ℕ) : ℝ)) * Real.log ((⌊y⌋₊ : ℕ) : ℝ) =
        y * Real.log ((⌊y⌋₊ : ℕ) : ℝ) -
          ((⌊y⌋₊ : ℕ) : ℝ) * Real.log ((⌊y⌋₊ : ℕ) : ℝ) := by
      ring
    rwa [hbridge] at hprod
  linarith

/-- Helper: `t * log t - t - (1/2) * log t` is monotone on `[2, ∞)`. -/
private theorem ctb_stirling_lower_mono (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    a * Real.log a - a - (1 / 2) * Real.log a ≤
      b * Real.log b - b - (1 / 2) * Real.log b := by
  have hpos_a : (0 : ℝ) < a := by linarith
  have hpos_b : (0 : ℝ) < b := by linarith
  have ha0 : a ≠ 0 := ne_of_gt hpos_a
  have hdiv : Real.log (b / a) = Real.log b - Real.log a :=
    Real.log_div (ne_of_gt hpos_b) (ne_of_gt hpos_a)
  have h1 : b - a ≤ b * (Real.log b - Real.log a) := by
    have hbase := Real.one_sub_inv_le_log_of_pos (div_pos hpos_b hpos_a)
    rw [hdiv, inv_div] at hbase
    have h := mul_le_mul_of_nonneg_left hbase (le_of_lt hpos_b)
    have hinv : b * (1 - a / b) = b - a := by
      rw [mul_sub, mul_one, ← mul_div_assoc,
        mul_div_cancel_left₀ _ (ne_of_gt hpos_b)]
    rwa [hinv] at h
  have h2 : Real.log b - Real.log a ≤ (b - a) / a := by
    have hbase2 := Real.log_le_sub_one_of_pos (div_pos hpos_b hpos_a)
    rw [hdiv] at hbase2
    have heq : b / a - 1 = (b - a) / a := by
      rw [sub_div, div_self ha0]
    rwa [heq] at hbase2
  have hla : 1 / (2 * a) ≤ Real.log a := by
    have hlog2 : (1 / 4 : ℝ) < Real.log 2 := by
      have h := Real.log_two_gt_d9
      linarith
    have hloga : Real.log 2 ≤ Real.log a :=
      Real.log_le_log (by norm_num) ha
    have hrec : 1 / (2 * a) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have h3' : (1 / 2) * ((b - a) / a) ≤ (b - a) * Real.log a := by
    have h := mul_le_mul_of_nonneg_left hla (sub_nonneg.mpr hab)
    have heq : (b - a) * (1 / (2 * a)) = (1 / 2) * ((b - a) / a) := by
      have h2a : (2 : ℝ) * a ≠ 0 := mul_ne_zero (by norm_num) ha0
      field_simp
    rwa [heq] at h
  have hb1 : b * (Real.log b - Real.log a) =
      b * Real.log b - b * Real.log a := mul_sub _ _ _
  have hb2 : b * Real.log a - a * Real.log a = (b - a) * Real.log a := by
    ring
  have hg1 : (1 / 2 : ℝ) * (Real.log b - Real.log a) =
      (1 / 2) * Real.log b - (1 / 2) * Real.log a := mul_sub _ _ _
  have h2s : (1 / 2 : ℝ) * (Real.log b - Real.log a) ≤
      (1 / 2) * ((b - a) / a) :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  linarith

/-- Lower Stirling bound at real arguments. -/
private theorem ctb_le_log_fact_floor (y : ℝ) (hy : 1 ≤ y) :
    y * Real.log y - y - (1 / 2) * Real.log y + 1 / 2 ≤
      Real.log ((⌊y⌋₊ ! : ℕ) : ℝ) := by
  have hn1 : 1 ≤ ⌊y⌋₊ := (Nat.one_le_floor_iff y).mpr hy
  have hpos_y : (0 : ℝ) < y := by linarith
  have hle : ((⌊y⌋₊ : ℕ) : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hlt : y < ((⌊y⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one y
  rcases eq_or_lt_of_le hn1 with hn_eq | hn_ge
  · -- Case `⌊y⌋₊ = 1`: the right side is `0`.
    have hn1' : ⌊y⌋₊ = 1 := hn_eq.symm
    rw [hn1', Nat.factorial_one, Nat.cast_one, Real.log_one]
    rw [hn1', Nat.cast_one] at hlt
    have hylt : y < 2 := by linarith
    have h1 : (y - 1 / 2) * Real.log y ≤ (y - 1 / 2) * (y - 1) :=
      mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hpos_y) (by linarith)
    have h2 : (y - 1 / 2) * (y - 1) ≤ y - 1 / 2 := by
      have hnn : (0 : ℝ) ≤ (2 - y) * (y - 1 / 2) :=
        mul_nonneg (by linarith) (by linarith)
      linear_combination hnn
    have hcomb : y * Real.log y - (1 / 2) * Real.log y =
        (y - 1 / 2) * Real.log y := by
      ring
    linarith
  · -- Case `⌊y⌋₊ ≥ 2`: Stirling's lower bound at `⌊y⌋₊ + 1`, then monotonicity.
    have hne : ⌊y⌋₊ + 1 ≠ 0 := by
      intro h
      omega
    have hS := Stirling.le_log_factorial_stirling hne
    have hfact : Real.log ((((⌊y⌋₊ + 1 : ℕ)) ! : ℕ) : ℝ) =
        Real.log (((⌊y⌋₊ + 1 : ℕ)) : ℝ) + Real.log ((⌊y⌋₊ ! : ℕ) : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul,
        Real.log_mul (by exact_mod_cast hne)
          (by exact_mod_cast Nat.factorial_ne_zero _)]
    have h2pi : (1 : ℝ) ≤ Real.log (2 * Real.pi) := by
      have hltpi : Real.exp 1 < 2 * Real.pi := by
        have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
        have hexp : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        linarith
      have h := Real.log_lt_log (Real.exp_pos 1) hltpi
      rw [Real.log_exp] at h
      linarith
    have hM : ((⌊y⌋₊ + 1 : ℕ) : ℝ) * Real.log ((⌊y⌋₊ + 1 : ℕ) : ℝ) -
        ((⌊y⌋₊ + 1 : ℕ) : ℝ) - (1 / 2) * Real.log ((⌊y⌋₊ + 1 : ℕ) : ℝ) +
        1 / 2 ≤ Real.log ((⌊y⌋₊ ! : ℕ) : ℝ) := by
      linarith [hS, hfact, h2pi]
    have h2y : (2 : ℝ) ≤ y := by
      have h2 : 2 ≤ ⌊y⌋₊ := hn_ge
      have h2r : (2 : ℝ) ≤ ((⌊y⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    have hab : y ≤ (((⌊y⌋₊ + 1 : ℕ)) : ℝ) := by
      have h := hlt
      push_cast at h ⊢
      linarith
    have hmono := ctb_stirling_lower_mono y (((⌊y⌋₊ + 1 : ℕ)) : ℝ) h2y hab
    linarith

/-- The Wanted constant equals `ctbA0`. -/
private theorem ctbA0_eq_wanted :
    Real.log (((2 : ℝ) ^ ((1 / 2 : ℝ)) * (3 : ℝ) ^ ((1 / 3 : ℝ)) *
      (5 : ℝ) ^ ((1 / 5 : ℝ))) / (30 : ℝ) ^ ((1 / 30 : ℝ))) = ctbA0 := by
  unfold ctbA0
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by norm_num) _, Real.log_rpow (by norm_num) _,
    Real.log_rpow (by norm_num) _, Real.log_rpow (by norm_num) _]

/-- `ctbA0` in the `(7/15, 3/10, 1/6)` form, hence positive. -/
private theorem ctbA0_eq' : ctbA0 =
    (7 / 15) * Real.log 2 + (3 / 10) * Real.log 3 + (1 / 6) * Real.log 5 := by
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    have e : (30 : ℝ) = 2 * 3 * 5 := by norm_num
    rw [e, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  unfold ctbA0
  rw [h30]
  ring

private theorem ctbA0_pos : 0 < ctbA0 := by
  rw [ctbA0_eq']
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h5 : (0 : ℝ) < Real.log 5 := Real.log_pos (by norm_num)
  have h2 := Real.log_two_gt_d9
  linarith

/-- `ctbA0 < 1`. -/
private theorem ctbA0_lt_one : ctbA0 < 1 := by
  have hl2 := Real.log_two_lt_d9
  have h3 : Real.log 3 = Real.log 2 + Real.log (3 / 2 : ℝ) := by
    have e : (3 : ℝ) = 2 * (3 / 2) := by norm_num
    conv_lhs => rw [e]
    rw [Real.log_mul (by norm_num) (by norm_num)]
  have h32 : Real.log (3 / 2 : ℝ) ≤ 1 / 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
    linarith
  have h5 : Real.log 5 = 2 * Real.log 2 + Real.log (5 / 4 : ℝ) := by
    have e : (5 : ℝ) = 2 ^ 2 * (5 / 4) := by norm_num
    conv_lhs => rw [e]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Nat.cast_ofNat]
  have h54 : Real.log (5 / 4 : ℝ) ≤ 1 / 4 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
    linarith
  rw [ctbA0_eq', h3, h5]
  linarith

/-- `5 * ctbA0 < (5/2) * log 5 + 1`. -/
private theorem ctb_fiveA0 : 5 * ctbA0 < (5 / 2) * Real.log 5 + 1 := by
  have hint : (2 : ℝ) ^ 8 * 3 ^ 9 < (5 : ℝ) ^ 10 := by norm_num
  have h := Real.log_lt_log (by positivity) hint
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow] at h
  simp only [Nat.cast_ofNat] at h
  have hl2 := Real.log_two_lt_d9
  rw [ctbA0_eq']
  linarith

/-- The signed five-term main-term identity. -/
private theorem ctb_main_identity (x : ℝ) (hx : 0 < x) :
    (x * Real.log x - x) - ((x / 2) * Real.log (x / 2) - (x / 2)) -
      ((x / 3) * Real.log (x / 3) - (x / 3)) -
      ((x / 5) * Real.log (x / 5) - (x / 5)) +
      ((x / 30) * Real.log (x / 30) - (x / 30)) = ctbA0 * x := by
  have e2 : Real.log (x / 2) = Real.log x - Real.log 2 :=
    Real.log_div (ne_of_gt hx) (by norm_num)
  have e3 : Real.log (x / 3) = Real.log x - Real.log 3 :=
    Real.log_div (ne_of_gt hx) (by norm_num)
  have e5 : Real.log (x / 5) = Real.log x - Real.log 5 :=
    Real.log_div (ne_of_gt hx) (by norm_num)
  have e30 : Real.log (x / 30) = Real.log x - Real.log 30 :=
    Real.log_div (ne_of_gt hx) (by norm_num)
  rw [e2, e3, e5, e30]
  unfold ctbA0
  ring

/-- Numeric side facts: `log 30 = log 2 + log 3 + log 5`. -/
private theorem ctb_log30_eq :
    Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
  have e : (30 : ℝ) = 2 * 3 * 5 := by norm_num
  conv_lhs => rw [e]
  rw [Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]

/-- Small factorials: `log (n!) ≤ (5/2) * log n` for `1 ≤ n < 5`. -/
private theorem ctb_log_fact_small (n : ℕ) (h1 : 1 ≤ n) (h5 : n < 5) :
    Real.log ((n ! : ℕ) : ℝ) ≤ (5 / 2) * Real.log (n : ℝ) := by
  have hfact : (((n ! : ℕ)) : ℝ) ^ 2 ≤ ((n : ℕ) : ℝ) ^ 5 := by
    have h : (n !) ^ 2 ≤ n ^ 5 := by
      interval_cases n <;> decide
    have h2 : ((((n !) ^ 2 : ℕ)) : ℝ) ≤ ((((n ^ 5 : ℕ))) : ℝ) :=
      Nat.cast_le.mpr h
    simpa [Nat.cast_pow] using h2
  have hfactpos : (0 : ℝ) < ((n ! : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hle := Real.log_le_log (pow_pos hfactpos 2) hfact
  rw [Real.log_pow, Real.log_pow] at hle
  simp only [Nat.cast_ofNat] at hle
  linarith

private theorem ctb_log6_pos : (0 : ℝ) < Real.log 6 :=
  Real.log_pos (by norm_num)

private theorem ctb_log6_lt_two : Real.log 6 < 2 := by
  by_contra hcon
  have hcon' : (2 : ℝ) ≤ Real.log 6 := le_of_not_gt hcon
  have hexp : (6 : ℝ) < Real.exp 2 := by
    have h1 := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      have e : (2 : ℝ) = 1 + 1 := by norm_num
      rw [e, Real.exp_add]
    nlinarith [sq_nonneg (Real.exp 1 - 2.7182818283), h1]
  have h := Real.exp_le_exp.mpr hcon'
  rw [Real.exp_log (by norm_num)] at h
  linarith

private theorem ctb_log30_gt_one : (1 : ℝ) < Real.log 30 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_one_lt_d9
  linarith

private theorem ctb_log150_gt_three : (3 : ℝ) < Real.log 150 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_one_lt_d9
  have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    have e : (3 : ℝ) = 1 + 1 + 1 := by norm_num
    rw [e, Real.exp_add, Real.exp_add]
    ring
  rw [e3]
  have hbound : Real.exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3 := by
    apply pow_lt_pow_left₀ h (le_of_lt (Real.exp_pos 1)) (by norm_num)
  have hnum : (2.7182818286 : ℝ) ^ 3 < 150 := by norm_num
  linarith

/-- Upper bound for `U(⌊x⌋₊)`. -/
private theorem ctbU_lt_upper (x : ℝ) (hx : 1 ≤ x) :
    ctbU ⌊x⌋₊ < ctbA0 * x + (5 / 2) * Real.log x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hle : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
  have f2 : ⌊x / 2⌋₊ = ⌊x⌋₊ / 2 := by
    have hcast : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    rw [hcast, Nat.floor_div_natCast]
  have f3 : ⌊x / 3⌋₊ = ⌊x⌋₊ / 3 := by
    have hcast : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
    rw [hcast, Nat.floor_div_natCast]
  have f5 : ⌊x / 5⌋₊ = ⌊x⌋₊ / 5 := by
    have hcast : (5 : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
    rw [hcast, Nat.floor_div_natCast]
  have f30 : ⌊x / 30⌋₊ = ⌊x⌋₊ / 30 := by
    have hcast : (30 : ℝ) = ((30 : ℕ) : ℝ) := by norm_num
    rw [hcast, Nat.floor_div_natCast]
  have e2 : Real.log (x / 2) = Real.log x - Real.log 2 :=
    Real.log_div (ne_of_gt hx0) (by norm_num)
  have e3 : Real.log (x / 3) = Real.log x - Real.log 3 :=
    Real.log_div (ne_of_gt hx0) (by norm_num)
  have e5 : Real.log (x / 5) = Real.log x - Real.log 5 :=
    Real.log_div (ne_of_gt hx0) (by norm_num)
  have e30 : Real.log (x / 30) = Real.log x - Real.log 30 :=
    Real.log_div (ne_of_gt hx0) (by norm_num)
  have hid := ctb_main_identity x hx0
  have h30 := ctb_log30_eq
  rcases lt_or_ge x 30 with hsmall | hbig
  · rcases lt_or_ge x 5 with hsmall5 | hmid
    · -- Case `1 ≤ x < 5`.
      have hn1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr (by linarith)
      have hn5 : ⌊x⌋₊ < 5 :=
        (Nat.floor_lt (by linarith)).mpr (by exact_mod_cast hsmall5)
      have hn30 : ⌊x⌋₊ / 30 = 0 := Nat.div_eq_of_lt (by omega)
      have hsmall := ctb_log_fact_small ⌊x⌋₊ hn1 hn5
      have hlogx : Real.log ((⌊x⌋₊ : ℕ) : ℝ) ≤ Real.log x :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊x⌋₊)) hle
      have hU : ctbU ⌊x⌋₊ ≤ Real.log ((⌊x⌋₊ ! : ℕ) : ℝ) := by
        unfold ctbU
        rw [hn30, Nat.factorial_zero, Nat.cast_one, Real.log_one]
        have hsub : ∀ d : ℕ, (0 : ℝ) ≤
            Real.log ((((⌊x⌋₊ / d : ℕ)) ! : ℕ) : ℝ) := by
          intro d
          apply Real.log_nonneg
          have h1d : 1 ≤ (⌊x⌋₊ / d)! :=
            Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
          exact_mod_cast h1d
        linarith [hsub 2, hsub 3, hsub 5]
      have hpos : 0 < ctbA0 * x := mul_pos ctbA0_pos hx0
      have hscale : (5 / 2 : ℝ) * Real.log ((⌊x⌋₊ : ℕ) : ℝ) ≤
          (5 / 2) * Real.log x :=
        mul_le_mul_of_nonneg_left hlogx (by norm_num)
      linarith
    · -- Case `5 ≤ x < 30`.
      have hn30 : ⌊x⌋₊ / 30 = 0 :=
        Nat.div_eq_of_lt ((Nat.floor_lt (by linarith)).mpr (by exact_mod_cast hsmall))
      have u0 := ctb_log_fact_floor_upper x (by linarith)
      have l2 := ctb_le_log_fact_floor (x / 2) (by linarith)
      rw [f2] at l2
      have l3 := ctb_le_log_fact_floor (x / 3) (by linarith)
      rw [f3] at l3
      have l5 := ctb_le_log_fact_floor (x / 5) (by linarith)
      rw [f5] at l5
      have hgt : -((x / 30) * Real.log (x / 30) - (x / 30)) ≤ 1 := by
        have ht0 : (0 : ℝ) < x / 30 := by linarith
        have h1 : Real.log ((x / 30)⁻¹) = -Real.log (x / 30) :=
          Real.log_inv _
        have h2 := Real.log_le_sub_one_of_pos
          (show (0 : ℝ) < (x / 30)⁻¹ by positivity)
        rw [h1] at h2
        have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt ht0)
        have heq : (x / 30) * ((x / 30)⁻¹ - 1) = 1 - (x / 30) := by
          rw [mul_sub, mul_inv_cancel₀ (ne_of_gt ht0), mul_one]
        rw [heq] at h3
        have hb : (x / 30) * (-Real.log (x / 30)) =
            -((x / 30) * Real.log (x / 30)) := by
          ring
        linarith
      have h30x : (150 : ℝ) ≤ 30 * x := by linarith
      have hlogle : Real.log 150 ≤ Real.log (30 * x) :=
        Real.log_le_log (by norm_num) h30x
      have hmul : Real.log (30 * x) = Real.log 30 + Real.log x :=
        Real.log_mul (by norm_num) (by linarith)
      unfold ctbU
      rw [hn30, Nat.factorial_zero, Nat.cast_one, Real.log_one]
      linarith [ctb_log150_gt_three]
  · -- Case `x ≥ 30`.
    have u0 := ctb_log_fact_floor_upper x (by linarith)
    have u30 := ctb_log_fact_floor_upper (x / 30) (by linarith)
    rw [f30] at u30
    have l2 := ctb_le_log_fact_floor (x / 2) (by linarith)
    rw [f2] at l2
    have l3 := ctb_le_log_fact_floor (x / 3) (by linarith)
    rw [f3] at l3
    have l5 := ctb_le_log_fact_floor (x / 5) (by linarith)
    rw [f5] at l5
    unfold ctbU
    linarith [ctb_log30_gt_one]

/-- Lower bound for `U(⌊x⌋₊)`. -/
private theorem ctb_lower_lt_U (x : ℝ) (hx : 1 < x) :
    ctbA0 * x - (5 / 2) * Real.log x - 1 < ctbU ⌊x⌋₊ := by
  have hx0 : (0 : ℝ) < x := by linarith
  have e2 : Real.log (x / 2) = Real.log x - Real.log 2 :=
    Real.log_div (ne_of_gt hx0) (by norm_num)
  have e3 : Real.log (x / 3) = Real.log x - Real.log 3 :=
    Real.log_div (ne_of_gt hx0) (by norm_num)
  have e5 : Real.log (x / 5) = Real.log x - Real.log 5 :=
    Real.log_div (ne_of_gt hx0) (by norm_num)
  have e30 : Real.log (x / 30) = Real.log x - Real.log 30 :=
    Real.log_div (ne_of_gt hx0) (by norm_num)
  have hid := ctb_main_identity x hx0
  have h30 := ctb_log30_eq
  have f2 : ⌊x / 2⌋₊ = ⌊x⌋₊ / 2 := by
    have hcast : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    rw [hcast, Nat.floor_div_natCast]
  have f3 : ⌊x / 3⌋₊ = ⌊x⌋₊ / 3 := by
    have hcast : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
    rw [hcast, Nat.floor_div_natCast]
  have f5 : ⌊x / 5⌋₊ = ⌊x⌋₊ / 5 := by
    have hcast : (5 : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
    rw [hcast, Nat.floor_div_natCast]
  have f30 : ⌊x / 30⌋₊ = ⌊x⌋₊ / 30 := by
    have hcast : (30 : ℝ) = ((30 : ℕ) : ℝ) := by norm_num
    rw [hcast, Nat.floor_div_natCast]
  rcases lt_or_ge x 30 with hsmall | hbig
  · rcases lt_or_ge x 5 with hsmall5 | hmid
    · -- Case `1 < x < 5`: `U ≥ 0` and the chord bound.
      have hU0 : (0 : ℝ) ≤ ctbU ⌊x⌋₊ := by
        rw [ctbU_eq_sum]
        apply Finset.sum_nonneg
        intro n _
        apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        exact_mod_cast ctbW_nonneg _
      set t : ℝ := (x - 1) / 4 with htdef
      have htx : x = 1 + 4 * t := by rw [htdef]; ring
      have ht0 : (0 : ℝ) ≤ t := by rw [htdef]; linarith
      have ht1 : t ≤ 1 := by rw [htdef]; linarith
      have hamgm := Real.geom_mean_le_arith_mean2_weighted
        (show (0 : ℝ) ≤ 1 - t by linarith) (show (0 : ℝ) ≤ t by linarith)
        (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 5 by norm_num)
        (show (1 - t) + t = 1 by ring)
      rw [Real.one_rpow, one_mul] at hamgm
      have hx5t : (5 : ℝ) ^ t ≤ x := by
        have heq : (1 - t) * 1 + t * 5 = x := by rw [htx]; ring
        rw [heq] at hamgm
        exact hamgm
      have hlogt : t * Real.log 5 ≤ Real.log x := by
        have h := Real.log_le_log (by positivity : (0 : ℝ) < (5 : ℝ) ^ t) hx5t
        rw [Real.log_rpow (by norm_num)] at h
        exact h
      have hc0 : ctbA0 - 1 < 0 := by linarith [ctbA0_lt_one]
      have hc1 : 5 * ctbA0 - (5 / 2) * Real.log 5 - 1 < 0 := by
        linarith [ctb_fiveA0]
      have hcomb : ctbA0 * x - (5 / 2) * (t * Real.log 5) - 1 =
          (1 - t) * (ctbA0 - 1) +
            t * (5 * ctbA0 - (5 / 2) * Real.log 5 - 1) := by
        rw [htx]
        ring
      have htc : (1 - t) * (ctbA0 - 1) +
          t * (5 * ctbA0 - (5 / 2) * Real.log 5 - 1) < 0 := by
        rcases eq_or_lt_of_le ht0 with h0 | hpos
        · rw [← h0]
          simpa using hc0
        · have e1 : (1 - t) * (ctbA0 - 1) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt hc0)
          have e2t : t * (5 * ctbA0 - (5 / 2) * Real.log 5 - 1) < 0 :=
            mul_neg_of_pos_of_neg hpos hc1
          linarith
      have hV : ctbA0 * x - (5 / 2) * (t * Real.log 5) - 1 < 0 := by
        linarith [hcomb, htc]
      have hscale : (5 / 2 : ℝ) * (t * Real.log 5) ≤ (5 / 2) * Real.log x :=
        mul_le_mul_of_nonneg_left hlogt (by norm_num)
      linarith
    · -- Case `5 ≤ x < 30`.
      have hn30 : ⌊x⌋₊ / 30 = 0 :=
        Nat.div_eq_of_lt ((Nat.floor_lt (by linarith)).mpr (by exact_mod_cast hsmall))
      have l0 := ctb_le_log_fact_floor x (by linarith)
      have u2 := ctb_log_fact_floor_upper (x / 2) (by linarith)
      rw [f2] at u2
      have u3 := ctb_log_fact_floor_upper (x / 3) (by linarith)
      rw [f3] at u3
      have u5 := ctb_log_fact_floor_upper (x / 5) (by linarith)
      rw [f5] at u5
      have hG30 : (x / 30) * Real.log (x / 30) - (x / 30) ≤ 0 := by
        have ht0 : (0 : ℝ) < x / 30 := by linarith
        have ht1 : x / 30 < 1 := by linarith
        have hneg : Real.log (x / 30) < 0 := Real.log_neg ht0 ht1
        have hprod : (x / 30) * Real.log (x / 30) < 0 :=
          mul_neg_of_pos_of_neg ht0 hneg
        linarith
      have h30x : (150 : ℝ) ≤ 30 * x := by linarith
      have hlogle : Real.log 150 ≤ Real.log (30 * x) :=
        Real.log_le_log (by norm_num) h30x
      have hmul : Real.log (30 * x) = Real.log 30 + Real.log x :=
        Real.log_mul (by norm_num) (by linarith)
      unfold ctbU
      rw [hn30, Nat.factorial_zero, Nat.cast_one, Real.log_one]
      linarith [ctb_log150_gt_three]
  · -- Case `x ≥ 30`.
    have l0 := ctb_le_log_fact_floor x (by linarith)
    have l30 := ctb_le_log_fact_floor (x / 30) (by linarith)
    rw [f30] at l30
    have u2 := ctb_log_fact_floor_upper (x / 2) (by linarith)
    rw [f2] at u2
    have u3 := ctb_log_fact_floor_upper (x / 3) (by linarith)
    rw [f3] at u3
    have u5 := ctb_log_fact_floor_upper (x / 5) (by linarith)
    rw [f5] at u5
    unfold ctbU
    linarith [ctb_log30_gt_one]

/-- Chebyshev's lower bound for `ψ`. -/
private theorem ctb_psi_lower (x : ℝ) (hx : 1 < x) :
    ctbA0 * x - (5 / 2) * Real.log x - 1 < Chebyshev.psi x := by
  have h := (ctb_sandwich_real x).2
  have h9 := ctb_lower_lt_U x hx
  linarith

/-- Auxiliary: the upper bound holds below `6 ^ k`. -/
private theorem ctb_psi_upper_aux (k : ℕ) : ∀ x : ℝ, 1 ≤ x → x < (6 : ℝ) ^ k →
    Chebyshev.psi x < (6 / 5) * ctbA0 * x +
      (5 / (4 * Real.log 6)) * (Real.log x) ^ 2 + (5 / 4) * Real.log x +
      1 := by
  have hL0 : Real.log 6 ≠ 0 := ne_of_gt ctb_log6_pos
  have hC : (0 : ℝ) ≤ 5 / (4 * Real.log 6) := by
    apply div_nonneg (by norm_num)
    apply mul_nonneg (by norm_num) (le_of_lt ctb_log6_pos)
  have hCL : (5 / (4 * Real.log 6)) * Real.log 6 = 5 / 4 := by
    field_simp
  induction k with
  | zero =>
    intro x hx1 hxlt
    rw [pow_zero] at hxlt
    linarith
  | succ k ih =>
    intro x hx1 hxlt
    have hx0 : (0 : ℝ) < x := by linarith
    have e6 : Real.log (x / 6) = Real.log x - Real.log 6 :=
      Real.log_div (ne_of_gt hx0) (by norm_num)
    have hle := (ctb_sandwich_real x).1
    have hU := ctbU_lt_upper x (by linarith)
    rcases lt_or_ge x 6 with hx6 | hx6
    · -- Base: `x < 6`, so `ψ (x / 6) = 0`.
      have hpsi6 : Chebyshev.psi (x / 6) = 0 :=
        Chebyshev.psi_eq_zero_of_lt_two (by linarith)
      rw [hpsi6, sub_zero] at hle
      have hψ : Chebyshev.psi x < ctbA0 * x + (5 / 2) * Real.log x := by
        linarith
      have g1 : (5 / (4 * Real.log 6)) * (Real.log 6 * Real.log x) =
          (5 / 4) * Real.log x := by
        rw [← mul_assoc, hCL]
      have g2 : (5 / (4 * Real.log 6)) * (Real.log 6 / 2) ^ 2 =
          (5 / 16) * Real.log 6 := by
        have e : (Real.log 6 / 2) ^ 2 =
            Real.log 6 * (Real.log 6 / 4) := by
          ring
        rw [e, ← mul_assoc, hCL]
        ring
      have hbridge : (5 / (4 * Real.log 6)) *
          (Real.log x - Real.log 6 / 2) ^ 2 =
          (5 / (4 * Real.log 6)) * (Real.log x) ^ 2 - (5 / 4) * Real.log x +
            (5 / 16) * Real.log 6 := by
        have e : (Real.log x - Real.log 6 / 2) ^ 2 = (Real.log x) ^ 2 -
            Real.log 6 * Real.log x + (Real.log 6 / 2) ^ 2 := by
          ring
        rw [e, mul_add, mul_sub, g1, g2]
      have hsq : (0 : ℝ) ≤ (5 / (4 * Real.log 6)) *
          (Real.log x - Real.log 6 / 2) ^ 2 :=
        mul_nonneg hC (sq_nonneg _)
      rw [hbridge] at hsq
      have hA0x : (0 : ℝ) < (1 / 5) * ctbA0 * x :=
        mul_pos (mul_pos (by norm_num) ctbA0_pos) hx0
      have hrem : (0 : ℝ) ≤ 1 - (5 / 16) * Real.log 6 := by
        have h := ctb_log6_lt_two
        linarith
      have hbase : (0 : ℝ) < (1 / 5) * ctbA0 * x +
          ((5 / (4 * Real.log 6)) * (Real.log x) ^ 2 - (5 / 4) * Real.log x +
            1) := by
        linarith
      linarith
    · -- Step: `ψ x ≤ U + ψ (x / 6)`, induction at `x / 6`.
      have h6k : x / 6 < (6 : ℝ) ^ k := by
        have e : (6 : ℝ) ^ (k + 1) = (6 : ℝ) ^ k * 6 := pow_succ _ _
        linarith
      have hIH := ih (x / 6) (by linarith) h6k
      rw [e6] at hIH
      have g3 : (5 / (4 * Real.log 6)) * (2 * Real.log 6 * Real.log x) =
          (5 / 2) * Real.log x := by
        have e : (2 : ℝ) * Real.log 6 * Real.log x =
            Real.log 6 * (2 * Real.log x) := by
          ring
        rw [e, ← mul_assoc, hCL]
        ring
      have g4 : (5 / (4 * Real.log 6)) * (Real.log 6) ^ 2 =
          (5 / 4) * Real.log 6 := by
        have e : (Real.log 6) ^ 2 = Real.log 6 * Real.log 6 := by ring
        rw [e, ← mul_assoc, hCL]
      have hsq2 : (5 / (4 * Real.log 6)) * (Real.log x - Real.log 6) ^ 2 =
          (5 / (4 * Real.log 6)) * (Real.log x) ^ 2 - (5 / 2) * Real.log x +
            (5 / 4) * Real.log 6 := by
        have e : (Real.log x - Real.log 6) ^ 2 = (Real.log x) ^ 2 -
            (2 * Real.log 6 * Real.log x) + (Real.log 6) ^ 2 := by
          ring
        rw [e, mul_add, mul_sub, g3, g4]
      have hm : (5 / 4 : ℝ) * (Real.log x - Real.log 6) =
          (5 / 4) * Real.log x - (5 / 4) * Real.log 6 := mul_sub _ _ _
      have hb6 : (6 / 5 : ℝ) * ctbA0 * (x / 6) = (1 / 5) * ctbA0 * x := by
        ring
      linarith

/-- Chebyshev's upper bound for `ψ`. -/
private theorem ctb_psi_upper (x : ℝ) (hx : 1 ≤ x) :
    Chebyshev.psi x < (6 / 5) * ctbA0 * x +
      (5 / (4 * Real.log 6)) * (Real.log x) ^ 2 + (5 / 4) * Real.log x +
      1 := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (y := (6 : ℝ)) x (by norm_num)
  exact ctb_psi_upper_aux k x hx hk

/-- Helper: pairing odd and even terms of a sum over `Icc 1 (2M+1)`. -/
private theorem ctb_pair_sum_le (b : ℕ → ℝ) (M : ℕ)
    (h : ∀ j ∈ Finset.Icc 1 M, b (2 * j + 1) ≤ b (2 * j)) :
    ∑ n ∈ Finset.Icc 1 (2 * M + 1), b n ≤
      b 1 + 2 * ∑ j ∈ Finset.Icc 1 M, b (2 * j) := by
  induction M with
  | zero =>
    rw [show (2 * 0 + 1 : ℕ) = 1 from rfl, Finset.Icc_self,
      Finset.sum_singleton]
    have hempty : ∑ j ∈ Finset.Icc 1 0, b (2 * j) = 0 := by
      rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from by decide,
        Finset.sum_empty]
    rw [hempty]
    linarith
  | succ M ih =>
    have hM : ∀ j ∈ Finset.Icc 1 M, b (2 * j + 1) ≤ b (2 * j) := by
      intro j hj
      apply h
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    have hpair := h (M + 1) (by simp)
    have eL : ∑ n ∈ Finset.Icc 1 (2 * (M + 1) + 1), b n =
        (∑ n ∈ Finset.Icc 1 (2 * M + 1), b n) + b (2 * (M + 1)) +
          b (2 * (M + 1) + 1) := by
      have e1 : 2 * (M + 1) + 1 = (2 * M + 1) + 1 + 1 := by ring
      rw [e1, Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
      have p1 : (2 * M + 1) + 1 + 1 = 2 * (M + 1) + 1 := by ring
      have p2 : (2 * M + 1) + 1 = 2 * (M + 1) := by ring
      rw [p1, p2]
    have eR : ∑ j ∈ Finset.Icc 1 (M + 1), b (2 * j) =
        (∑ j ∈ Finset.Icc 1 M, b (2 * j)) + b (2 * (M + 1)) := by
      have e1 : M + 1 = M + 1 := rfl
      rw [e1, Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
    rw [eL, eR]
    linarith [ih hM, hpair]

/-- `θ x ≤ ψ x - ψ √x`. -/
private theorem ctb_theta_le (x : ℝ) (hx : 1 ≤ x) :
    Chebyshev.theta x ≤ Chebyshev.psi x - Chebyshev.psi (Real.sqrt x) := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hge := Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi hx0
  have e : Real.sqrt x = x ^ ((2 : ℝ)⁻¹) := by
    rw [Real.sqrt_eq_rpow, show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ from by norm_num]
  rw [e]
  have h3 := Chebyshev.psi_nonneg (x ^ ((3 : ℝ)⁻¹))
  have h7 := Chebyshev.psi_nonneg (x ^ ((7 : ℝ)⁻¹))
  linarith

/-- `ψ x - 2 ψ √x ≤ θ x`. -/
private theorem ctb_psi_lower_theta (x : ℝ) (hx : 1 ≤ x) :
    Chebyshev.psi x - 2 * Chebyshev.psi (Real.sqrt x) ≤ Chebyshev.theta x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have h1x : (1 : ℝ) ≤ x := hx
  have hmono : ∀ j ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
      Chebyshev.theta (x ^ ((1 : ℝ) / (((2 * j + 1 : ℕ)) : ℝ))) ≤
      Chebyshev.theta (x ^ ((1 : ℝ) / (((2 * j : ℕ)) : ℝ))) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hj1 : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hj.1
    have h2j : (0 : ℝ) < (((2 * j : ℕ)) : ℝ) := by
      have h0 : 0 < 2 * j := by omega
      exact_mod_cast h0
    have hle : (((2 * j : ℕ)) : ℝ) ≤ ((((2 * j + 1 : ℕ))) : ℝ) := by
      have h0 : 2 * j ≤ 2 * j + 1 := Nat.le_succ _
      exact_mod_cast h0
    apply Chebyshev.theta_mono
    apply Real.rpow_le_rpow_of_exponent_le h1x
    exact one_div_le_one_div_of_le h2j hle
  have hMle : ⌊Real.log (Real.sqrt x) / Real.log 2⌋₊ ≤
      ⌊Real.log x / Real.log 2⌋₊ := by
    apply Nat.floor_le_floor
    have hlogsqrt : Real.log (Real.sqrt x) ≤ Real.log x := by
      rw [Real.log_sqrt hx0]
      have hlogx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
      linarith
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    gcongr
  have h1 : Chebyshev.psi x =
      ∑ n ∈ Finset.Icc 1 (2 * ⌊Real.log x / Real.log 2⌋₊ + 1),
        Chebyshev.theta (x ^ ((1 : ℝ) / ((n : ℕ) : ℝ))) :=
    Chebyshev.psi_eq_sum_theta' hx0 (by omega)
  have hcomb : ∑ n ∈ Finset.Icc 1 (2 * ⌊Real.log x / Real.log 2⌋₊ + 1),
        Chebyshev.theta (x ^ ((1 : ℝ) / ((n : ℕ) : ℝ))) ≤
      Chebyshev.theta (x ^ ((1 : ℝ) / ((((1 : ℕ))) : ℝ))) +
        2 * ∑ j ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
          Chebyshev.theta (x ^ ((1 : ℝ) / ((((2 * j : ℕ))) : ℝ))) :=
    ctb_pair_sum_le (fun n => Chebyshev.theta (x ^ ((1 : ℝ) / ((n : ℕ) : ℝ))))
      _ (fun j hj => hmono j hj)
  have hpsi2 : Chebyshev.psi (Real.sqrt x) =
      ∑ j ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        Chebyshev.theta (x ^ ((1 : ℝ) / ((((2 * j : ℕ))) : ℝ))) := by
    have hbase := Chebyshev.psi_eq_sum_theta'
      (Real.sqrt_nonneg x) hMle
    rw [hbase]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hj0 : ((j : ℕ) : ℝ) ≠ 0 := by
      have h0 : j ≠ 0 := by omega
      exact_mod_cast h0
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0]
    congr 1
    rw [Nat.cast_mul, Nat.cast_ofNat]
    have hj0' : ((j : ℕ) : ℝ) ≠ 0 := hj0
    field_simp
  have hb1 : Chebyshev.theta (x ^ ((1 : ℝ) / ((((1 : ℕ))) : ℝ))) =
      Chebyshev.theta x := by
    congr 1
    rw [Nat.cast_one, div_one, Real.rpow_one]
  linarith

section
namespace MetaMathlibExt

/--
**Chebyshev's explicit bounds for the theta function.** Let $\theta(x) = \sum_{p \le x} \log p$,
the sum running over primes, and let
$$A = \log \frac{2^{1/2} \, 3^{1/3} \, 5^{1/5}}{30^{1/30}}.$$
Then for every real $x > 1$,
$$\theta(x) < \frac{6}{5}Ax - A\sqrt{x} + \frac{5}{4\log 6}(\log x)^2 + \frac{5}{2}\log x + 2$$
and
$$\theta(x) > Ax - \frac{12}{5}A\sqrt{x} - \frac{5}{8\log 6}(\log x)^2 - \frac{15}{4}\log x - 3.$$

Source: S. Nazardonyavi and S. Yakubovich, "Extremely Abundant Numbers and
the Riemann Hypothesis," Journal of Integer Sequences 17 (2014),
Article 14.2.8, Lemma citing Chebyshev p. 379, lines 288-298,
<https://cs.uwaterloo.ca/journals/JIS/VOL17/Nazar/nazar4.tex>; original
result: P. L. Chebyshev's memoir on prime numbers.

Proves `Wanted` entry `chebyshev_theta_explicit_bounds`.
-/
public theorem chebyshev_theta_explicit_bounds (x : ℝ) (hx : 1 < x) :
    let A : ℝ :=
      Real.log (((2 : ℝ) ^ ((1 / 2 : ℝ)) * (3 : ℝ) ^ ((1 / 3 : ℝ)) *
        (5 : ℝ) ^ ((1 / 5 : ℝ))) / (30 : ℝ) ^ ((1 / 30 : ℝ)));
    Chebyshev.theta x <
      (6 / 5 : ℝ) * A * x - A * Real.sqrt x +
      (5 / (4 * Real.log 6)) * (Real.log x) ^ 2 +
      (5 / 2 : ℝ) * Real.log x + 2 ∧
    Chebyshev.theta x >
      A * x - (12 / 5 : ℝ) * A * Real.sqrt x -
      (5 / (8 * Real.log 6)) * (Real.log x) ^ 2 -
      (15 / 4 : ℝ) * Real.log x - 3 := by
  intro A
  have hA : A = ctbA0 := ctbA0_eq_wanted
  rw [hA]
  have hx0 : (0 : ℝ) < x := by linarith
  have hs1 : (1 : ℝ) < Real.sqrt x := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hx
    rw [Real.sqrt_one] at h
    exact h
  have hL0 : Real.log 6 ≠ 0 := ne_of_gt ctb_log6_pos
  have h12a := ctb_theta_le x (le_of_lt hx)
  have h12b := ctb_psi_lower_theta x (le_of_lt hx)
  have h10x := ctb_psi_lower x hx
  have h11x := ctb_psi_upper x (by linarith)
  have h10s := ctb_psi_lower (Real.sqrt x) hs1
  have h11s := ctb_psi_upper (Real.sqrt x) (le_of_lt hs1)
  have hsq_log : Real.log (Real.sqrt x) = Real.log x / 2 :=
    Real.log_sqrt (le_of_lt hx0)
  rw [hsq_log] at h10s h11s
  refine ⟨?_, ?_⟩
  · linarith
  · have hsq_bridge : 2 * ((5 / (4 * Real.log 6)) * (Real.log x / 2) ^ 2) =
        (5 / (8 * Real.log 6)) * (Real.log x) ^ 2 := by
      field_simp
      ring
    linarith

end MetaMathlibExt
