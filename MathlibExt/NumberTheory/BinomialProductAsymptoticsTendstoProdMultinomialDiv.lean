/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Multinomial
public import MathlibExt.NumberTheory.BinomialProductAsymptotics
import MathlibExt.NumberTheory.CentralBinomialProductAsymptotics
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Asymptotics of products of multinomial coefficients

This module gives the limiting normalized product of multinomial coefficients and the bounds
on its factorial-product constant.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 5.
-/

namespace MetaMathlibExt

open Filter Topology
open LogFactorialExpansion

private theorem log_factorial_add (n k : ℕ) :
    Real.log ((n + k).factorial : ℝ) = Real.log n.factorial +
      ∑ j ∈ Finset.range k, Real.log (n + j + 1 : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show n + (k + 1) = (n + k) + 1 by omega, log_factorial_succ, ih,
      Finset.sum_range_succ]
    push_cast
    ring

private theorem weightedLog_add (n k : ℕ) :
    weightedLog (n + k) = weightedLog n +
      ∑ j ∈ Finset.range k, (n + j + 1 : ℝ) * Real.log (n + j + 1 : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show n + (k + 1) = (n + k) + 1 by omega, weightedLog_succ, ih,
      Finset.sum_range_succ]
    push_cast
    ring

private theorem log_factorial_product (k n : ℕ) (hk : 0 < k) :
    ∑ ν ∈ Finset.Icc 1 n, Real.log ((k * ν).factorial : ℝ) =
      (n + 1 : ℝ) * Real.log (k * n).factorial - weightedLog (k * n) / k -
        ∑ j ∈ Finset.range k, (1 - (j + 1 : ℝ) / k) *
          ∑ l ∈ Finset.range n, Real.log (k * l + j + 1 : ℝ) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  induction n with
  | zero => simp [weightedLog]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp_rw [Finset.sum_range_succ, mul_add]
    simp only [Nat.mul_one]
    rw [Finset.sum_add_distrib, log_factorial_add, weightedLog_add]
    push_cast
    rw [add_div, Finset.sum_div]
    have he : ∑ j ∈ Finset.range k,
        ((k * n + j + 1 : ℝ) * Real.log (k * n + j + 1 : ℝ) / k +
          (1 - (j + 1 : ℝ) / k) * Real.log (k * n + j + 1 : ℝ)) =
        (n + 1 : ℝ) * ∑ j ∈ Finset.range k, Real.log (k * n + j + 1 : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      field_simp
      ring
    rw [Finset.sum_add_distrib] at he
    linear_combination he

private theorem log_arithmetic_product_limit (k j : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ =>
      (∑ l ∈ Finset.range n, Real.log (k * l + j + 1 : ℝ)) -
        (n * Real.log k + Real.log n.factorial +
          ((j + 1 : ℝ) / k - 1) * Real.log n))
      atTop (𝓝 (-Real.log (Real.Gamma ((j + 1 : ℝ) / k)))) := by
  let x : ℝ := (j + 1 : ℝ) / k
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : 0 < x := by dsimp [x]; positivity
  have hg := (Real.GammaSeq_tendsto_Gamma x).log (Real.Gamma_pos_of_pos hx).ne'
  have hi : Tendsto (fun n : ℕ => x / n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul x
  have hl := (hi.const_add 1).log (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have h := hg.neg.sub hl
  simp only [add_zero, Real.log_one, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : ∀ l ∈ Finset.range (n + 1), 0 < x + l := fun l _ => by positivity
  have hsum : ∑ l ∈ Finset.range n, Real.log (k * l + j + 1 : ℝ) =
      n * Real.log k + ∑ l ∈ Finset.range n, Real.log (x + l) := by
    have hconst : ∑ l ∈ Finset.range n, Real.log k = n * Real.log k := by simp
    rw [← hconst, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [← Real.log_mul hk0.ne' (by positivity : x + l ≠ 0)]
    congr 1
    dsimp [x]
    field_simp
    ring
  rw [hsum, Real.GammaSeq, Real.log_div (by positivity)
    (Finset.prod_ne_zero_iff.mpr fun l hl => (hp l hl).ne'),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hn0,
    Real.log_prod (fun l hl => (hp l hl).ne'), Finset.sum_range_succ]
  have hshift : 1 + x / n = (x + n) / n := by field_simp; ring
  rw [hshift, Real.log_div (by positivity) hn0.ne']
  ring

private theorem sum_successor_moments (k : ℕ) :
    (∑ j ∈ Finset.range k, (j + 1 : ℝ)) = k * (k + 1) / 2 ∧
      (∑ j ∈ Finset.range k, (j + 1 : ℝ) ^ 2) = k * (k + 1) * (2 * k + 1) / 6 := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Finset.sum_range_succ, ih.1, ih.2, Nat.cast_add, Nat.cast_one]
    constructor <;> ring

private theorem sum_fraction_moments (k : ℕ) (hk : 0 < k) :
    (∑ j ∈ Finset.range k, (j + 1 : ℝ) / k) = (k + 1) / 2 ∧
      (∑ j ∈ Finset.range k, ((j + 1 : ℝ) / k) ^ 2) =
        (k + 1) * (2 * k + 1) / (6 * k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  constructor
  · rw [← Finset.sum_div, (sum_successor_moments k).1]
    field_simp
  · simp_rw [div_pow]
    rw [← Finset.sum_div, (sum_successor_moments k).2]
    field_simp

private theorem sum_log_arithmetic (k n : ℕ) :
    (∑ j ∈ Finset.range k, ∑ l ∈ Finset.range n,
      Real.log (k * l + j + 1 : ℝ)) = Real.log (k * n).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [Finset.sum_range_succ]
    rw [Finset.sum_add_distrib, ih, Nat.mul_add, Nat.mul_one, log_factorial_add]
    push_cast
    rfl

private theorem sum_log_gamma_fraction (k : ℕ) (hk : 0 < k) :
    (∑ j ∈ Finset.range k, Real.log (Real.Gamma ((j + 1 : ℝ) / k))) =
      (k - 1 : ℝ) / 2 * Real.log (2 * Real.pi) - Real.log k / 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hd : Tendsto (fun n : ℕ => k * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n ≤ k * n; exact Nat.le_mul_of_pos_left n hk)
      tendsto_id
  have hs := tendsto_finsetSum (Finset.range k)
    (fun j _ => log_arithmetic_product_limit k j hk)
  have hf := factorialError_limit
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  let c : ℝ := Real.log k / 2 + (1 - k : ℝ) / 2 * Real.log (2 * Real.pi)
  have he := (((hf.comp hd).sub (hf.const_mul (k : ℝ))).add
    (hi.const_mul ((1 / k - k : ℝ) / 12))).add_const c
  simp only [mul_zero, sub_zero, add_zero, zero_add] at he
  have hsame : (fun n : ℕ =>
      ∑ j ∈ Finset.range k, ((∑ l ∈ Finset.range n,
        Real.log (k * l + j + 1 : ℝ)) -
        (n * Real.log k + Real.log n.factorial +
          ((j + 1 : ℝ) / k - 1) * Real.log n))) =ᶠ[atTop]
      (fun n : ℕ => factorialError (k * n) - k * factorialError n +
        (1 / k - k : ℝ) / 12 * (n : ℝ)⁻¹ + c) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Finset.sum_sub_distrib, sum_log_arithmetic]
    simp_rw [add_assoc, Finset.sum_add_distrib, ← Finset.sum_mul,
      Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      (sum_fraction_moments k hk).1]
    unfold factorialError factorialMain c
    push_cast
    rw [Real.log_mul hk0.ne' hn0.ne']
    field_simp
    ring
  have h := tendsto_nhds_unique hs (he.congr' hsame.symm)
  rw [Finset.sum_neg_distrib] at h
  dsimp [c] at h
  linear_combination -h

private theorem sum_fraction_weights (k : ℕ) (hk : 0 < k) :
    (∑ j ∈ Finset.range k, (1 - (j + 1 : ℝ) / k)) = (k - 1 : ℝ) / 2 ∧
      (∑ j ∈ Finset.range k, (1 - (j + 1 : ℝ) / k) *
        ((j + 1 : ℝ) / k - 1)) = -(k - 1 : ℝ) * (2 * k - 1) / (6 * k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hm := sum_fraction_moments k hk
  constructor
  · rw [Finset.sum_sub_distrib, hm.1]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    ring
  · simp_rw [show ∀ x : ℝ, (1 - x) * (x - 1) = 2 * x - x ^ 2 - 1 by intro x; ring,
      Finset.sum_sub_distrib, ← Finset.mul_sum, hm.1, hm.2]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    field_simp
    ring

private noncomputable def arithmeticError (k j n : ℕ) : ℝ :=
  (∑ l ∈ Finset.range n, Real.log (k * l + j + 1 : ℝ)) -
    (n * Real.log k + Real.log n.factorial +
      ((j + 1 : ℝ) / k - 1) * Real.log n) +
    Real.log (Real.Gamma ((j + 1 : ℝ) / k))

private theorem arithmeticError_limit (k j : ℕ) (hk : 0 < k) :
    Tendsto (arithmeticError k j) atTop (𝓝 0) := by
  unfold arithmeticError
  simpa only [neg_add_cancel] using
    (log_arithmetic_product_limit k j hk).add_const
      (Real.log (Real.Gamma ((j + 1 : ℝ) / k)))

private noncomputable def commonLogScale (n : ℕ) : ℝ :=
  Real.log glaisherKinkelinConstant - 3 / 4 * (n : ℝ) ^ 2 - n / 2 +
    ((n : ℝ) * (n + 1) / 2 + 1 / 12) * Real.log n

private noncomputable def normalizedFactorialLog (k n : ℕ) : ℝ :=
  (∑ ν ∈ Finset.Icc 1 n, Real.log ((k * ν).factorial : ℝ)) -
    Real.log (factorialProductComparison k n) - k * commonLogScale n

private theorem log_factorialProductComparison (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    Real.log (factorialProductComparison k n) =
      k * Real.log k * (n * (n + 1) / 2) +
        n / 2 * (Real.log (2 * Real.pi) + Real.log k - 1 + Real.log n) +
        ((3 * (k : ℝ) + 1) / (12 * k)) * Real.log n := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold factorialProductComparison
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_pow,
    Real.log_div, Real.log_exp]
  ring

private theorem normalizedFactorialLog_error (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    normalizedFactorialLog k n -
        (Real.log (factorialProductConstant k) + Real.log (2 * Real.pi) / 4) =
      (n + 1 : ℝ) * factorialError (k * n) - weightedError (k * n) / k -
        (k - 1 : ℝ) / 2 * factorialError n -
        (∑ j ∈ Finset.range k, (1 - (j + 1 : ℝ) / k) * arithmeticError k j n) +
        (1 / (12 * k) - (k - 1 : ℝ) / 24) * (n : ℝ)⁻¹ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ha (j : ℕ) : (∑ l ∈ Finset.range n, Real.log (k * l + j + 1 : ℝ)) =
      n * Real.log k + Real.log n.factorial + ((j + 1 : ℝ) / k - 1) * Real.log n -
        Real.log (Real.Gamma ((j + 1 : ℝ) / k)) + arithmeticError k j n := by
    unfold arithmeticError
    ring
  unfold normalizedFactorialLog
  rw [log_factorial_product k n hk, log_factorialProductComparison k n hk hn]
  simp_rw [ha]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← mul_assoc, ← Finset.sum_mul,
    (sum_fraction_weights k hk).1, (sum_fraction_weights k hk).2]
  have hg : (∑ j ∈ Finset.range k,
      (1 - (j + 1 : ℝ) / k) * Real.log (Real.Gamma ((j + 1 : ℝ) / k))) =
      (k - 1 : ℝ) / 2 * Real.log (2 * Real.pi) - Real.log k / 2 -
        ∑ j ∈ Finset.range k,
          (j + 1 : ℝ) / k * Real.log (Real.Gamma ((j + 1 : ℝ) / k)) := by
    simp_rw [sub_mul, one_mul, Finset.sum_sub_distrib]
    rw [sum_log_gamma_fraction k hk]
  rw [hg, factorialProductConstant, Real.log_exp]
  have hi : (∑ ν ∈ Finset.Ico 1 k,
      (ν : ℝ) / k * Real.log (Real.Gamma ((ν : ℝ) / k))) =
      ∑ j ∈ Finset.range k,
        (j + 1 : ℝ) / k * Real.log (Real.Gamma ((j + 1 : ℝ) / k)) := by
    have he : (∑ ν ∈ Finset.Ico 1 (k + 1),
        (ν : ℝ) / k * Real.log (Real.Gamma ((ν : ℝ) / k))) =
        ∑ ν ∈ Finset.Ico 1 k,
          (ν : ℝ) / k * Real.log (Real.Gamma ((ν : ℝ) / k)) := by
      rw [Finset.sum_Ico_succ_top (by omega)]
      simp only [div_self hk0.ne', Real.Gamma_one, Real.log_one, mul_zero, add_zero]
    rw [← he, ← Finset.sum_Ico_add' (fun ν : ℕ =>
      (ν : ℝ) / k * Real.log (Real.Gamma ((ν : ℝ) / k))) 0 k 1]
    simp only [Nat.Ico_zero_eq_range, Nat.cast_add, Nat.cast_one]
  rw [hi]
  unfold commonLogScale factorialError weightedError factorialMain weightedMain
  push_cast
  rw [Real.log_mul hk0.ne' hn0.ne']
  field_simp
  ring

private theorem normalizedFactorialLog_limit (k : ℕ) (hk : 0 < k) :
    Tendsto (normalizedFactorialLog k) atTop
      (𝓝 (Real.log (factorialProductConstant k) + Real.log (2 * Real.pi) / 4)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hd : Tendsto (fun n : ℕ => k * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n ≤ k * n; exact Nat.le_mul_of_pos_left n hk)
      tendsto_id
  have hf := factorialError_limit
  have hF := error_limits.1.comp hd
  have hW := error_limits.2.comp hd
  have hnf := (hF.div_const (k : ℝ)).add (hf.comp hd)
  simp only [zero_div, add_zero] at hnf
  have hnf' : Tendsto (fun n : ℕ => (n + 1 : ℝ) * factorialError (k * n))
      atTop (𝓝 0) := hnf.congr (fun n => by
    dsimp [Function.comp_def]
    push_cast
    field_simp)
  have hA := tendsto_finsetSum (Finset.range k) (fun j _ =>
    (arithmeticError_limit k j hk).const_mul (1 - (j + 1 : ℝ) / k))
  simp only [mul_zero, Finset.sum_const_zero] at hA
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := (((hnf'.sub (hW.div_const (k : ℝ))).sub
    (hf.const_mul ((k - 1 : ℝ) / 2))).sub hA).add
    (hi.const_mul (1 / (12 * k) - (k - 1 : ℝ) / 24))
  simp only [zero_div, mul_zero, sub_zero, add_zero] at h
  have hl := h.add_const (Real.log (factorialProductConstant k) +
    Real.log (2 * Real.pi) / 4)
  simp only [zero_add] at hl
  refine hl.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have he := normalizedFactorialLog_error k n hk hn
  dsimp [Function.comp_def]
  linear_combination -he

private theorem log_multinomial (r : ℕ) (b : Fin r → ℕ) (n : ℕ) :
    Real.log (Nat.multinomial Finset.univ (fun i => b i * n) : ℝ) =
      Real.log ((∑ i, b i) * n).factorial -
        ∑ i, Real.log (b i * n).factorial := by
  have h : (∏ i, ((b i * n).factorial : ℝ)) *
      (Nat.multinomial Finset.univ (fun i => b i * n) : ℝ) =
      (((∑ i, b i) * n).factorial : ℝ) := by
    exact_mod_cast (by simpa only [← Finset.sum_mul] using
      Nat.multinomial_spec Finset.univ (fun i => b i * n))
  have hp : ∀ i : Fin r, (0 : ℝ) < (b i * n).factorial := fun i => by positivity
  have hm : (0 : ℝ) < Nat.multinomial Finset.univ (fun i => b i * n) := by
    exact_mod_cast Nat.multinomial_pos Finset.univ (fun i => b i * n)
  have he := congrArg Real.log h
  rw [Real.log_mul (Finset.prod_pos (fun i _ => hp i)).ne' hm.ne',
    Real.log_prod (fun i _ => (hp i).ne')] at he
  linear_combination he

private theorem log_multinomial_product (r : ℕ) (b : Fin r → ℕ) (n : ℕ) :
    Real.log (∏ ν ∈ Finset.Icc 1 n,
        (Nat.multinomial Finset.univ (fun i => b i * ν) : ℝ)) =
      (∑ ν ∈ Finset.Icc 1 n, Real.log (((∑ i, b i) * ν).factorial : ℝ)) -
        ∑ i, ∑ ν ∈ Finset.Icc 1 n, Real.log ((b i * ν).factorial : ℝ) := by
  rw [Real.log_prod (fun ν _ => by
    exact_mod_cast (Nat.multinomial_pos Finset.univ (fun i => b i * ν)).ne')]
  simp_rw [log_multinomial, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

private theorem multinomial_log_limit (r : ℕ) (hr : 2 ≤ r) (b : Fin r → ℕ)
    (hb : ∀ i, 1 ≤ b i) :
    Tendsto (fun n : ℕ =>
      Real.log (∏ ν ∈ Finset.Icc 1 n,
        (Nat.multinomial Finset.univ (fun i => b i * ν) : ℝ)) -
      Real.log (factorialProductComparison (∑ i, b i) n /
        ∏ i, factorialProductComparison (b i) n))
      atTop (𝓝 (Real.log (factorialProductConstant (∑ i, b i)) -
        (∑ i, Real.log (factorialProductConstant (b i))) +
        (1 - (r : ℝ)) / 4 * Real.log (2 * Real.pi))) := by
  have ha : r ≤ ∑ i, b i := by
    simpa using (Finset.sum_le_sum (s := Finset.univ) (f := fun _ : Fin r => 1)
      (g := b) (fun i _ => hb i))
  have ha0 : 0 < ∑ i, b i := by omega
  have h := (normalizedFactorialLog_limit _ ha0).sub
    (tendsto_finsetSum Finset.univ (fun i _ =>
      normalizedFactorialLog_limit (b i) (by have := hb i; omega)))
  have he : Real.log (factorialProductConstant (∑ i, b i)) + Real.log (2 * Real.pi) / 4 -
      (∑ i, (Real.log (factorialProductConstant (b i)) + Real.log (2 * Real.pi) / 4)) =
      Real.log (factorialProductConstant (∑ i, b i)) -
        (∑ i, Real.log (factorialProductConstant (b i))) +
        (1 - (r : ℝ)) / 4 * Real.log (2 * Real.pi) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [he] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hp : ∀ i, 0 < factorialProductComparison (b i) n := fun i => by
    have hi : 0 < b i := by have := hb i; omega
    unfold factorialProductComparison
    positivity
  have hpa : 0 < factorialProductComparison (∑ i, b i) n := by
    unfold factorialProductComparison
    positivity
  rw [log_multinomial_product,
    Real.log_div hpa.ne' (Finset.prod_pos (fun i _ => hp i)).ne',
    Real.log_prod (fun i _ => (hp i).ne')]
  unfold normalizedFactorialLog
  simp_rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Nat.cast_sum]
  ring

private noncomputable def stirlingRemainder (n : ℕ) : ℝ :=
  Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi)

private theorem stirlingRemainder_limit : Tendsto stirlingRemainder atTop (𝓝 0) := by
  unfold stirlingRemainder
  simpa only [sub_self] using
    ((Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).sub_const
      (Real.log (Real.sqrt Real.pi)))

private theorem stirlingRemainder_lower_step (n : ℕ) (hn : 0 < n) :
    1 / (12 * n + 1 : ℝ) - 1 / (12 * (n + 1) + 1) ≤
      stirlingRemainder n - stirlingRemainder (n + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h := le_hasSum (Stirling.log_stirlingSeq_sdiff_hasSum m) 0
    (fun j _ => by positivity)
  norm_num at h
  unfold stirlingRemainder
  have hp : (0 : ℝ) < m + 1 := by positivity
  calc
    _ ≤ 1 / (3 * (2 * (m + 1) + 1) ^ 2 : ℝ) := by
      push_cast
      field_simp
      nlinarith
    _ ≤ _ := by
      simp only [Nat.succ_eq_add_one]
      field_simp at h ⊢
      linarith

private theorem stirlingRemainder_bounds (n : ℕ) (hn : 0 < n) :
    1 / (12 * n + 1 : ℝ) ≤ stirlingRemainder n ∧
      stirlingRemainder n ≤ 1 / (12 * n : ℝ) := by
  have ht : Tendsto (fun n : ℕ => (12 * (n + 1) : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n => by
      have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith) tendsto_natCast_atTop_atTop
  have ht' : Tendsto (fun n : ℕ => (12 * (n + 1) + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n => by
      have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith) tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (1 : ℝ) / (12 * (n + 1))) atTop (𝓝 0) :=
    by simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp ht
  have hi' : Tendsto (fun n : ℕ => (1 : ℝ) / (12 * (n + 1) + 1)) atTop (𝓝 0) :=
    by simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp ht'
  have hl := (stirlingRemainder_limit.comp (tendsto_add_atTop_nat 1)).sub hi'
  have hu := (stirlingRemainder_limit.comp (tendsto_add_atTop_nat 1)).sub hi
  simp only [sub_zero] at hl hu
  have hanti : Antitone (fun n : ℕ => stirlingRemainder (n + 1) -
      1 / (12 * (n + 1) + 1 : ℝ)) := by
    apply antitone_nat_of_succ_le
    intro n
    have h := stirlingRemainder_lower_step (n + 1) (by omega)
    push_cast at h ⊢
    linarith
  have hmono : Monotone (fun n : ℕ => stirlingRemainder (n + 1) -
      1 / (12 * (n + 1) : ℝ)) := by
    apply monotone_nat_of_le_succ
    intro n
    have h := Stirling.log_stirlingSeq_sdiff_le (n + 1)
    unfold stirlingRemainder
    push_cast at h ⊢
    have he : 1 / (12 * (n + 1) : ℝ) - 1 / (12 * (n + 1 + 1)) =
        1 / (12 * (n + 1) * (n + 1 + 1) : ℝ) := by field_simp; ring
    rw [← he] at h
    linarith
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  constructor
  · have h := hanti.le_of_tendsto hl m
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    linarith
  · have h := hmono.ge_of_tendsto hu m
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    linarith

private theorem log_factorial_stirlingRemainder (n : ℕ) (hn : 0 < n) :
    Real.log (n.factorial : ℝ) =
      (n : ℝ) * Real.log n - n + Real.log (2 * Real.pi * n) / 2 +
        stirlingRemainder n := by
  unfold stirlingRemainder
  rw [Stirling.log_stirlingSeq_formula]
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_exp,
    Real.log_sqrt]
  ring

private theorem sum_Icc_cast (n : ℕ) :
    (∑ ν ∈ Finset.Icc 1 n, (ν : ℝ)) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

private theorem sum_Icc_log (n : ℕ) :
    (∑ ν ∈ Finset.Icc 1 n, Real.log ν) = Real.log (n.factorial : ℝ) := by
  rw [← Real.sum_log_eq_log_factorial, ← Finset.Icc_add_one_left_eq_Ioc]
  rfl

private theorem sum_stirlingRemainder_identity (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    normalizedFactorialLog k n - Real.log (2 * Real.pi) / 4 =
      (∑ ν ∈ Finset.Icc 1 n, stirlingRemainder (k * ν)) -
        Real.log n / (12 * k) + k * weightedError n + factorialError n / 2 +
        1 / (24 * n : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (∑ ν ∈ Finset.Icc 1 n, Real.log ((k * ν).factorial : ℝ)) =
      k * Real.log k * (n * (n + 1) / 2) + k * weightedLog n -
        k * (n * (n + 1) / 2) + n / 2 * Real.log (2 * Real.pi) +
        n / 2 * Real.log k + Real.log n.factorial / 2 +
        ∑ ν ∈ Finset.Icc 1 n, stirlingRemainder (k * ν) := by
    have ht : ∀ ν ∈ Finset.Icc 1 n, Real.log ((k * ν).factorial : ℝ) =
        k * Real.log k * ν + k * ((ν : ℝ) * Real.log ν) - k * ν +
          Real.log (2 * Real.pi) / 2 + Real.log k / 2 + Real.log ν / 2 +
          stirlingRemainder (k * ν) := by
      intro ν hν
      have hν0 : 0 < ν := (Finset.mem_Icc.mp hν).1
      rw [log_factorial_stirlingRemainder (k * ν) (Nat.mul_pos hk hν0)]
      push_cast
      simp (disch := positivity) only [Real.log_mul]
      ring
    rw [Finset.sum_congr rfl ht]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_div, sum_Icc_cast, sum_Icc_log, Finset.sum_const,
      Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    unfold weightedLog
    ring
  unfold normalizedFactorialLog
  rw [he, log_factorialProductComparison k n hk hn]
  unfold commonLogScale weightedError weightedMain factorialError factorialMain
  field_simp
  ring

private theorem sum_stirlingRemainder_limit (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => (∑ ν ∈ Finset.Icc 1 n, stirlingRemainder (k * ν)) -
        Real.log n / (12 * k)) atTop (𝓝 (Real.log (factorialProductConstant k))) := by
  have hi : Tendsto (fun n : ℕ => 1 / (24 * n : ℝ)) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => (24 * n : ℝ)) atTop atTop :=
      tendsto_atTop_mono (fun n => by
        have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith) tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp ht
  have h := ((((normalizedFactorialLog_limit k hk).sub_const
    (Real.log (2 * Real.pi) / 4)).sub (error_limits.2.const_mul (k : ℝ))).sub
    (factorialError_limit.div_const 2)).sub hi
  simp only [add_sub_cancel_right, mul_zero, zero_div, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have he := sum_stirlingRemainder_identity k n hk hn
  linear_combination he

private theorem sum_Icc_inv (n : ℕ) :
    (∑ ν ∈ Finset.Icc 1 n, (1 : ℝ) / ν) = harmonic n := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp only [one_div]

private theorem sum_Icc_inv_sq_bound (n : ℕ) :
    (∑ ν ∈ Finset.Icc 1 n, (1 : ℝ) / (ν : ℝ) ^ 2) ≤ 2 := by
  have hs (n : ℕ) : (∑ ν ∈ Finset.Icc 1 (n + 1), (1 : ℝ) / (ν : ℝ) ^ 2) ≤
      2 - 1 / (n + 1 : ℝ) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have he : (1 : ℝ) / (n + 2 : ℝ) ^ 2 ≤
          1 / (n + 1 : ℝ) - 1 / (n + 2 : ℝ) := by
        field_simp
        nlinarith
      push_cast at ih ⊢
      rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
      linarith
  cases n with
  | zero => norm_num
  | succ n => exact (hs n).trans (sub_le_self _ (by positivity))

private theorem log_factorialProductConstant_bounds (k : ℕ) (hk : 0 < k) :
    1 / (36 * k : ℝ) < Real.log (factorialProductConstant k) ∧
      Real.log (factorialProductConstant k) < 1 / (18 * k : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hg := Real.tendsto_harmonic_sub_log.div_const (12 * k : ℝ)
  have hF := sum_stirlingRemainder_limit k hk
  have hu : Real.log (factorialProductConstant k) ≤
      Real.eulerMascheroniConstant / (12 * k) := by
    apply le_of_tendsto_of_tendsto hF hg
    filter_upwards [] with n
    rw [sub_div, ← sum_Icc_inv]
    gcongr
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro ν hν
    have hν0 : 0 < ν := (Finset.mem_Icc.mp hν).1
    have h := (stirlingRemainder_bounds (k * ν) (Nat.mul_pos hk hν0)).2
    push_cast at h
    convert h using 1
    field_simp
  have hl : Real.eulerMascheroniConstant / (12 * k) - 1 / (72 * (k : ℝ) ^ 2) ≤
      Real.log (factorialProductConstant k) := by
    apply le_of_tendsto_of_tendsto (hg.sub_const (1 / (72 * (k : ℝ) ^ 2))) hF
    filter_upwards [] with n
    have hs : ∑ ν ∈ Finset.Icc 1 n, ((1 : ℝ) / ν / (12 * k) -
        1 / (144 * (k : ℝ) ^ 2) * (1 / (ν : ℝ) ^ 2)) ≤
        ∑ ν ∈ Finset.Icc 1 n, stirlingRemainder (k * ν) := by
      apply Finset.sum_le_sum
      intro ν hν
      have hν0 : 0 < ν := (Finset.mem_Icc.mp hν).1
      have hνr : (0 : ℝ) < ν := by exact_mod_cast hν0
      have h := (stirlingRemainder_bounds (k * ν) (Nat.mul_pos hk hν0)).1
      apply le_trans _ h
      push_cast
      field_simp
      nlinarith
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum, sum_Icc_inv] at hs
    have hb := mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_bound n)
      (by positivity : 0 ≤ 1 / (144 * (k : ℝ) ^ 2))
    have he : 1 / (144 * (k : ℝ) ^ 2) * 2 = 1 / (72 * (k : ℝ) ^ 2) := by ring
    rw [he] at hb
    rw [sub_div]
    linarith
  constructor
  · apply lt_of_lt_of_le _ hl
    have hγ := Real.one_half_lt_eulerMascheroniConstant
    have hγk := mul_lt_mul_of_pos_right hγ hk0
    rw [lt_sub_iff_add_lt]
    field_simp
    nlinarith
  · apply lt_of_le_of_lt hu
    have hγ := Real.eulerMascheroniConstant_lt_two_thirds
    have hγk := mul_lt_mul_of_pos_right hγ hk0
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith

private theorem factorialProductConstant_ratio_bounds (r : ℕ) (hr : 2 ≤ r)
    (b : Fin r → ℕ) (hb : ∀ i, 1 ≤ b i) :
    factorialProductConstant (∑ i, b i) / (∏ i, factorialProductConstant (b i)) ∈
      Set.Ioo 0 1 := by
  have ha : r ≤ ∑ i, b i := by
    simpa using (Finset.sum_le_sum (s := Finset.univ) (f := fun _ : Fin r => 1)
      (g := b) (fun i _ => hb i))
  have ha0 : 0 < ∑ i, b i := by omega
  have hpa := factorialProductConstant_pos (∑ i, b i)
  have hpb := Finset.prod_pos (fun i (_ : i ∈ Finset.univ) =>
    factorialProductConstant_pos (b i))
  have hp := div_pos hpa hpb
  refine ⟨hp, ?_⟩
  have hbi (i : Fin r) : 1 / (36 * (∑ i, b i) : ℝ) <
      Real.log (factorialProductConstant (b i)) := by
    have hi : 0 < b i := by have := hb i; omega
    have hia : b i ≤ ∑ i, b i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hia' : (b i : ℝ) ≤ ∑ i, (b i : ℝ) := by exact_mod_cast hia
    have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 36 * b i)
      (mul_le_mul_of_nonneg_left hia' (by norm_num : (0 : ℝ) ≤ 36))
    simpa only [Nat.cast_sum] using
      h.trans_lt (log_factorialProductConstant_bounds (b i) hi).1
  have hs : (r : ℝ) * (1 / (36 * (∑ i, b i) : ℝ)) <
      ∑ i, Real.log (factorialProductConstant (b i)) := by
    have hs := Finset.sum_lt_sum (s := Finset.univ) (fun i _ => (hbi i).le)
      ⟨⟨0, by omega⟩, Finset.mem_univ _, hbi ⟨0, by omega⟩⟩
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hs
  have hs' : 1 / (18 * (∑ i, b i) : ℝ) <
      ∑ i, Real.log (factorialProductConstant (b i)) := by
    apply lt_of_le_of_lt _ hs
    have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have he : 1 / (18 * (∑ i, b i) : ℝ) =
        2 * (1 / (36 * (∑ i, b i) : ℝ)) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hr' (by positivity)
  apply (Real.log_lt_log_iff hp (by norm_num : (0 : ℝ) < 1)).mp
  rw [Real.log_one, Real.log_div hpa.ne' hpb.ne',
    Real.log_prod (fun i _ => (factorialProductConstant_pos (b i)).ne'), sub_neg]
  exact (log_factorialProductConstant_bounds _ ha0).2.trans hs'

@[expose] public section

/-- **Asymptotics of products of multinomial coefficients.** Let $r \ge 2$, let
$b_1, \dots, b_r \ge 1$ be natural numbers with $a = b_1 + \dots + b_r$, let $F_k$ denote the
factorial product constants and $P_k$ the factorial comparison functions, and put
$c_{a,b} = F_a / (F_{b_1} \cdots F_{b_r})$. As $m \to \infty$, the ratio of
$\prod_{n=1}^{m} \binom{an}{b_1 n, \dots, b_r n}$ to $P_a(m) / (P_{b_1}(m) \cdots P_{b_r}(m))$
tends to $c_{a,b} (2\pi)^{(1-r)/4}$; moreover $0 < c_{a,b} < 1$.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 5. -/
public theorem tendsto_prod_multinomial_div (r : ℕ) (hr : 2 ≤ r) (b : Fin r → ℕ)
    (hb : ∀ i, 1 ≤ b i) :
    Tendsto (fun m : ℕ => (∏ n ∈ Finset.Icc 1 m,
        (Nat.multinomial Finset.univ (fun i => b i * n) : ℝ)) /
        (factorialProductComparison (∑ i, b i) m /
          ∏ i, factorialProductComparison (b i) m))
      atTop (𝓝 (factorialProductConstant (∑ i, b i) / (∏ i, factorialProductConstant (b i)) *
        (2 * Real.pi) ^ ((1 - (r : ℝ)) / 4))) ∧
      factorialProductConstant (∑ i, b i) / (∏ i, factorialProductConstant (b i)) ∈
        Set.Ioo 0 1 := by
  constructor
  · have h := Real.continuous_exp.continuousAt.tendsto.comp
      (multinomial_log_limit r hr b hb)
    have hpa := factorialProductConstant_pos (∑ i, b i)
    have hpb := Finset.prod_pos (fun i (_ : i ∈ Finset.univ) =>
      factorialProductConstant_pos (b i))
    have hlog : Real.log (factorialProductConstant (∑ i, b i)) -
        (∑ i, Real.log (factorialProductConstant (b i))) =
        Real.log (factorialProductConstant (∑ i, b i) /
          (∏ i, factorialProductConstant (b i))) := by
      rw [Real.log_div hpa.ne' hpb.ne',
        Real.log_prod (fun i _ => (factorialProductConstant_pos (b i)).ne')]
    rw [hlog, Real.exp_add, Real.exp_log (div_pos hpa hpb)] at h
    have he : Real.exp ((1 - (r : ℝ)) / 4 * Real.log (2 * Real.pi)) =
        (2 * Real.pi) ^ ((1 - (r : ℝ)) / 4) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      congr 1
      ring
    rw [he] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have ha : r ≤ ∑ i, b i := by
      simpa using (Finset.sum_le_sum (s := Finset.univ) (f := fun _ : Fin r => 1)
        (g := b) (fun i _ => hb i))
    have ha0 : 0 < ∑ i, b i := by omega
    have hp : 0 < (∏ ν ∈ Finset.Icc 1 n,
        (Nat.multinomial Finset.univ (fun i => b i * ν) : ℝ)) :=
      Finset.prod_pos (fun ν _ => by
        exact_mod_cast Nat.multinomial_pos Finset.univ (fun i => b i * ν))
    have hq : 0 < factorialProductComparison (∑ i, b i) n /
        ∏ i, factorialProductComparison (b i) n := by
      apply div_pos
      · unfold factorialProductComparison
        positivity
      · apply Finset.prod_pos
        intro i _
        have hi : 0 < b i := by have := hb i; omega
        unfold factorialProductComparison
        positivity
    dsimp only [Function.comp_apply]
    rw [← Real.log_div hp.ne' hq.ne', Real.exp_log (div_pos hp hq)]
  · exact factorialProductConstant_ratio_bounds r hr b hb

end

end MetaMathlibExt
