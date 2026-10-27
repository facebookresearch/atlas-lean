/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import MathlibExt.NumberTheory.ArithmeticFunction.MoebiusSeries

/-!
# Average orders of `φ`, `σ`, `d` and `φ(n) / n`

We prove the classical elementary asymptotics for the summatory functions of Euler's totient
`φ`, the divisor sum `σ 1`, the divisor-counting function `d = σ 0` and the totient ratio
`φ(n) / n`, together with the sum of the integers up to `x` coprime to a fixed `k`. All sums
run over the positive integers `n ≤ x`, written `Finset.Ioc 0 ⌊x⌋₊` as for `Chebyshev.psi`.

The two quadratic results come from a general statement: if `|g| ≤ 1` then
`∑_{n ≤ x} (g * id)(n) = (∑ g(d) / d²) x² / 2 + O(x log x)`, and similarly if `|g(d)| ≤ 1 / d`
then `∑_{n ≤ x} (g * ζ)(n) = (∑ g(d) / d) x + O(log x)`.

## Main statements

* `ArithmeticFunction.abs_sum_Ioc_mul_id_sub_le`,
  `ArithmeticFunction.sum_Ioc_mul_id_sub_isBigO`: the mean value of `g * id` for `|g| ≤ 1`.
* `ArithmeticFunction.abs_sum_Ioc_mul_zeta_sub_le`: the mean value of `g * ζ` for
  `|g(d)| ≤ 1 / d`.
* `Nat.sum_totient_sub_isBigO`, `Nat.sum_totient_isEquivalent`:
  `∑_{n ≤ x} φ(n) = (3 / π²) x² + O(x log x)`.
* `ArithmeticFunction.sum_sigma_one_sub_isBigO`, `ArithmeticFunction.sum_sigma_one_isEquivalent`:
  `∑_{n ≤ x} σ(n) = (π² / 12) x² + O(x log x)`.
* `Nat.abs_sum_totient_div_sub_le`, `Nat.sum_totient_div_sub_isBigO`:
  `∑_{n ≤ x} φ(n) / n = (6 / π²) x + O(log x)`.
* `ArithmeticFunction.abs_sum_sigma_zero_sub_mul_log_le`,
  `ArithmeticFunction.sum_sigma_zero_sub_mul_log_isBigO`: `∑_{n ≤ x} d(n) = x log x + O(x)`.
* `Nat.abs_sum_coprime_sub_totient_div_mul_sq_le`:
  `∑_{n ≤ x, (n, k) = 1} n = φ(k) / (2k) · x² + O(d(k) x)`, uniformly in `k` and `x`.
-/

@[expose] public section

open Finset Filter Asymptotics Real

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.sigma

namespace ArithmeticFunction

/-! ### Auxiliary estimates -/

/-- The tail of a series dominated by `∑ 1 / d²`: if `|f d| ≤ 1 / d²` for every `d`, then
`|∑' d, f d - ∑_{d ≤ N} f d| ≤ 2 / (N + 1)`. -/
private theorem abs_tsum_sub_sum_Ioc_le {f : ℕ → ℝ} (hf : ∀ d, |f d| ≤ 1 / (d : ℝ) ^ 2)
    (N : ℕ) : |∑' d, f d - ∑ d ∈ Ioc 0 N, f d| ≤ 2 / ((N : ℝ) + 1) := by
  have hsum2 : Summable (fun d : ℕ => 1 / (d : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have hfs : Summable f :=
    Summable.of_norm_bounded hsum2 fun d => by rw [Real.norm_eq_abs]; exact hf d
  have h0 : f 0 = 0 := by simpa using hf 0
  have hrange : ∑ d ∈ range (N + 1), f d = ∑ d ∈ Ioc 0 N, f d := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos N), h0, zero_add]
    rfl
  have hgt : Summable (fun i : ℕ => 1 / ((i + (N + 1) : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff (f := fun d : ℕ => 1 / (d : ℝ) ^ 2) (N + 1)).mpr hsum2
  have hnt : Summable (fun i : ℕ => ‖f (i + (N + 1))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun i => by rw [Real.norm_eq_abs]; exact hf _) hgt
  have hfinal : ∑' i : ℕ, 1 / ((i + (N + 1) : ℕ) : ℝ) ^ 2 ≤ 2 / ((N : ℝ) + 1) := by
    refine hgt.tsum_le_of_sum_range_le fun M => ?_
    have hre : ∑ i ∈ range M, 1 / ((i + (N + 1) : ℕ) : ℝ) ^ 2
        = ∑ j ∈ Ico (N + 1) (N + 1 + M), 1 / ((j : ℕ) : ℝ) ^ 2 := by
      rw [sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left]
      exact sum_congr rfl fun i _ => by rw [Nat.add_comm]
    rw [hre, Finset.Ico_add_one_left_eq_Ioo]
    simpa only [one_div] using sum_Ioo_inv_sq_le (α := ℝ) N (N + 1 + M)
  have heq : ∑' d, f d - ∑ d ∈ Ioc 0 N, f d = ∑' i, f (i + (N + 1)) := by
    rw [← hrange, ← hfs.sum_add_tsum_nat_add (N + 1)]
    ring
  rw [heq, ← Real.norm_eq_abs]
  calc ‖∑' i, f (i + (N + 1))‖ ≤ ∑' i, ‖f (i + (N + 1))‖ := norm_tsum_le_tsum_norm hnt
    _ ≤ ∑' i : ℕ, 1 / ((i + (N + 1) : ℕ) : ℝ) ^ 2 :=
        hnt.tsum_le_tsum (fun i => by rw [Real.norm_eq_abs]; exact hf _) hgt
    _ ≤ 2 / ((N : ℝ) + 1) := hfinal

/-- `{1, …, N} = (0, N]`. -/
private theorem Icc_one_eq_Ioc_zero (N : ℕ) : Icc 1 N = Ioc 0 N := by
  ext n
  simp only [mem_Icc, mem_Ioc]
  omega

/-- The harmonic sum `∑_{d ≤ N} 1 / d` is at most `1 + log N`. -/
private theorem sum_Ioc_one_div_le (N : ℕ) : ∑ d ∈ Ioc 0 N, (1 : ℝ) / d ≤ 1 + log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa only [one_div, Icc_one_eq_Ioc_zero] using h

/-- `∑_{m ≤ M} m = M (M + 1) / 2`. -/
private theorem sum_Ioc_natCast (M : ℕ) : ∑ m ∈ Ioc 0 M, (m : ℝ) = M * (M + 1) / 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih]
    push_cast
    ring

/-- `x log x` is negligible against `c x²` for `c ≠ 0`. -/
private theorem isLittleO_mul_log_const_mul_sq {c : ℝ} (hc : c ≠ 0) :
    (fun x : ℝ => x * log x) =o[atTop] fun x => c * x ^ 2 := by
  have h := ((isBigO_refl (fun x : ℝ => x) atTop).mul_isLittleO isLittleO_log_id_atTop)
    |>.const_mul_right hc
  refine h.congr_right fun x => ?_
  simp [sq]

/-- An `O(x log x)` error term is negligible against a main term `c x²` with `c ≠ 0`. -/
private theorem isEquivalent_of_sub_isBigO_mul_log {u : ℝ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : (fun x => u x - c * x ^ 2) =O[atTop] fun x => x * log x) :
    u ~[atTop] fun x => c * x ^ 2 :=
  h.trans_isLittleO (isLittleO_mul_log_const_mul_sq hc)

/-! ### Mean values of `g * id` and `g * ζ` -/

/-- If `|g n| ≤ 1` for all `n`, then
`|∑_{n ≤ N} (g * id)(n) - (∑' d, g d / d²) / 2 · N²| ≤ N / 2 · (1 + log N) + N`. -/
theorem abs_sum_Ioc_mul_id_sub_le (g : ArithmeticFunction ℝ) (hg : ∀ n, |g n| ≤ 1) (N : ℕ) :
    |∑ n ∈ Ioc 0 N, (g * (ArithmeticFunction.id : ArithmeticFunction ℝ)) n
        - (∑' d, g d / (d : ℝ) ^ 2) / 2 * (N : ℝ) ^ 2|
      ≤ (N : ℝ) / 2 * (1 + log N) + N := by
  have hS : ∑ n ∈ Ioc 0 N, (g * (ArithmeticFunction.id : ArithmeticFunction ℝ)) n
      = ∑ d ∈ Ioc 0 N, g d * (((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2) := by
    rw [sum_Ioc_mul_eq_sum_sum]
    refine sum_congr rfl fun d _ => ?_
    rw [← sum_Ioc_natCast]
    simp
  have hfg : ∀ d : ℕ, |g d / (d : ℝ) ^ 2| ≤ 1 / (d : ℝ) ^ 2 := fun d => by
    rw [abs_div, abs_of_nonneg (sq_nonneg (d : ℝ))]
    exact div_le_div_of_nonneg_right (hg d) (sq_nonneg _)
  -- The truncated main term, compared term by term.
  have h1 : |∑ n ∈ Ioc 0 N, (g * (ArithmeticFunction.id : ArithmeticFunction ℝ)) n
        - (∑ d ∈ Ioc 0 N, g d / (d : ℝ) ^ 2) / 2 * (N : ℝ) ^ 2|
      ≤ (N : ℝ) / 2 * (1 + log N) := by
    have hmain : (∑ d ∈ Ioc 0 N, g d / (d : ℝ) ^ 2) / 2 * (N : ℝ) ^ 2
        = ∑ d ∈ Ioc 0 N, g d * (((N : ℝ) / d) ^ 2 / 2) := by
      rw [sum_div, sum_mul]
      refine sum_congr rfl fun d _ => ?_
      rw [div_pow]
      ring
    rw [hS, hmain, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans <|
      (sum_le_sum (g := fun d : ℕ => (N : ℝ) / 2 * (1 / (d : ℝ))) fun d hd => ?_).trans ?_
    · have hd0 : 0 < d := (mem_Ioc.mp hd).1
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
      have hmq : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
      have hqm : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
        rw [div_lt_iff₀ hdR]
        exact_mod_cast (Nat.div_lt_iff_lt_mul hd0).1 (Nat.lt_succ_self (N / d))
      have hq0 : (0 : ℝ) ≤ (N : ℝ) / d := by positivity
      have hm0 : (0 : ℝ) ≤ ((N / d : ℕ) : ℝ) := Nat.cast_nonneg _
      have hbd : |((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2 - ((N : ℝ) / d) ^ 2 / 2|
          ≤ (N : ℝ) / d / 2 := by
        rw [abs_le]
        constructor <;> nlinarith [mul_le_mul hmq hmq hm0 hq0,
          mul_le_mul_of_nonneg_left hqm.le hq0, mul_le_mul_of_nonneg_left hqm.le hm0]
      rw [← mul_sub, abs_mul]
      refine (mul_le_mul (hg d) hbd (abs_nonneg _) zero_le_one).trans_eq ?_
      ring
    · rw [← mul_sum]
      gcongr
      exact sum_Ioc_one_div_le N
  -- The tail of the series.
  have h2 : |(∑ d ∈ Ioc 0 N, g d / (d : ℝ) ^ 2) / 2 * (N : ℝ) ^ 2
      - (∑' d, g d / (d : ℝ) ^ 2) / 2 * (N : ℝ) ^ 2| ≤ (N : ℝ) := by
    rw [← sub_mul, ← sub_div, abs_mul, abs_div, abs_sub_comm, abs_two,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)]
    calc |∑' d, g d / (d : ℝ) ^ 2 - ∑ d ∈ Ioc 0 N, g d / (d : ℝ) ^ 2| / 2 * (N : ℝ) ^ 2
        ≤ 2 / ((N : ℝ) + 1) / 2 * (N : ℝ) ^ 2 := by
          gcongr
          exact abs_tsum_sub_sum_Ioc_le hfg N
      _ = (N : ℝ) * ((N : ℝ) / ((N : ℝ) + 1)) := by field_simp
      _ ≤ N := mul_le_of_le_one_right (Nat.cast_nonneg N)
          (div_le_one_of_le₀ (by linarith) (by positivity))
  exact (abs_sub_le _ _ _).trans (add_le_add h1 h2)

/-- Passing from `N : ℕ` to real `x` in a quadratic mean-value estimate. -/
private theorem isBigO_of_abs_sub_const_mul_sq_le {S : ℕ → ℝ} {c : ℝ}
    (h : ∀ N : ℕ, |S N - c * (N : ℝ) ^ 2| ≤ (N : ℝ) / 2 * (1 + log N) + N) :
    (fun x : ℝ => S ⌊x⌋₊ - c * x ^ 2) =O[atTop] fun x => x * log x := by
  refine isBigO_iff.2 ⟨2 + 2 * |c|, ?_⟩
  filter_upwards [eventually_ge_atTop (exp 1)] with x hx
  have hx1 : 1 ≤ x := le_trans (one_le_exp zero_le_one) hx
  have hlog : 1 ≤ log x := (le_log_iff_exp_le (by linarith)).2 hx
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hN1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (Nat.one_le_floor_iff x).2 hx1
  have hlogN : log ⌊x⌋₊ ≤ log x := log_le_log (by linarith) hNx
  have hlogN0 : 0 ≤ log ⌊x⌋₊ := log_nonneg hN1
  have hsq : |c * (⌊x⌋₊ : ℝ) ^ 2 - c * x ^ 2| ≤ 2 * |c| * x := by
    rw [← mul_sub, abs_mul]
    have : |(⌊x⌋₊ : ℝ) ^ 2 - x ^ 2| ≤ 2 * x := by
      rw [abs_le]
      constructor <;> nlinarith
    nlinarith [abs_nonneg c]
  have hxlog : x ≤ x * log x := le_mul_of_one_le_right (by linarith) hlog
  have hNlog : (⌊x⌋₊ : ℝ) * log ⌊x⌋₊ ≤ x * log x :=
    mul_le_mul hNx hlogN hlogN0 (by linarith)
  have hcx : 2 * |c| * x ≤ 2 * |c| * (x * log x) :=
    mul_le_mul_of_nonneg_left hxlog (by positivity)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by nlinarith : 0 ≤ x * log x)]
  calc |S ⌊x⌋₊ - c * x ^ 2|
      ≤ |S ⌊x⌋₊ - c * (⌊x⌋₊ : ℝ) ^ 2| + |c * (⌊x⌋₊ : ℝ) ^ 2 - c * x ^ 2| := abs_sub_le _ _ _
    _ ≤ (⌊x⌋₊ : ℝ) / 2 * (1 + log ⌊x⌋₊) + ⌊x⌋₊ + 2 * |c| * x := add_le_add (h _) hsq
    _ ≤ (2 + 2 * |c|) * (x * log x) := by nlinarith

/-- If `|g n| ≤ 1` for all `n`, then `∑_{n ≤ x} (g * id)(n) = (∑' d, g d / d²) / 2 · x² +
O(x log x)`. -/
theorem sum_Ioc_mul_id_sub_isBigO (g : ArithmeticFunction ℝ) (hg : ∀ n, |g n| ≤ 1) :
    (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, (g * (ArithmeticFunction.id : ArithmeticFunction ℝ)) n
        - (∑' d, g d / (d : ℝ) ^ 2) / 2 * x ^ 2) =O[atTop] fun x => x * log x :=
  isBigO_of_abs_sub_const_mul_sq_le (S := fun N =>
    ∑ n ∈ Ioc 0 N, (g * (ArithmeticFunction.id : ArithmeticFunction ℝ)) n)
    (abs_sum_Ioc_mul_id_sub_le g hg)

/-- If `|g d| ≤ 1 / d` for all `d`, then
`|∑_{n ≤ N} (g * ζ)(n) - (∑' d, g d / d) · N| ≤ 3 + log N`. -/
theorem abs_sum_Ioc_mul_zeta_sub_le (g : ArithmeticFunction ℝ) (hg : ∀ n, |g n| ≤ 1 / n)
    (N : ℕ) :
    |∑ n ∈ Ioc 0 N, (g * (ζ : ArithmeticFunction ℝ)) n - (∑' d, g d / d) * N| ≤ 3 + log N := by
  have hfg : ∀ d : ℕ, |g d / d| ≤ 1 / (d : ℝ) ^ 2 := fun d => by
    rw [abs_div, Nat.abs_cast, sq, ← div_div]
    gcongr
    exact hg d
  have h1 : |∑ n ∈ Ioc 0 N, (g * (ζ : ArithmeticFunction ℝ)) n
      - (∑ d ∈ Ioc 0 N, g d / d) * N| ≤ 1 + log N := by
    rw [sum_Ioc_mul_zeta_eq_sum, sum_mul, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans <|
      (sum_le_sum (g := fun d : ℕ => 1 / (d : ℝ)) fun d hd => ?_).trans (sum_Ioc_one_div_le N)
    have hd0 : 0 < d := (mem_Ioc.mp hd).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hmq : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
    have hqm : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hdR]
      exact_mod_cast (Nat.div_lt_iff_lt_mul hd0).1 (Nat.lt_succ_self (N / d))
    have e1 : |((N / d : ℕ) : ℝ) - N / d| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    rw [show g d * ((N / d : ℕ) : ℝ) - g d / d * N = g d * (((N / d : ℕ) : ℝ) - N / d) by ring,
      abs_mul]
    exact (mul_le_mul (hg d) e1 (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have h2 : |(∑ d ∈ Ioc 0 N, g d / d) * N - (∑' d, g d / d) * N| ≤ 2 := by
    rw [← sub_mul, abs_mul, abs_sub_comm, Nat.abs_cast]
    calc |∑' d, g d / d - ∑ d ∈ Ioc 0 N, g d / d| * N ≤ 2 / ((N : ℝ) + 1) * N := by
          gcongr
          exact abs_tsum_sub_sum_Ioc_le hfg N
      _ ≤ 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          linarith
  calc _ ≤ (1 + log N) + 2 := (abs_sub_le _ _ _).trans (add_le_add h1 h2)
    _ = 3 + log N := by ring

/-- If `|g d| ≤ 1 / d` for all `d`, then for real `x ≥ 1`,
`|∑_{n ≤ x} (g * ζ)(n) - (∑' d, g d / d) · x| ≤ log x + 5`. -/
theorem abs_sum_Ioc_floor_mul_zeta_sub_le (g : ArithmeticFunction ℝ) (hg : ∀ n, |g n| ≤ 1 / n)
    {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (g * (ζ : ArithmeticFunction ℝ)) n - (∑' d, g d / d) * x|
      ≤ log x + 5 := by
  have hfg : ∀ d : ℕ, |g d / d| ≤ 1 / (d : ℝ) ^ 2 := fun d => by
    rw [abs_div, Nat.abs_cast, sq, ← div_div]
    gcongr
    exact hg d
  have hc : |∑' d, g d / (d : ℝ)| ≤ 2 := by
    simpa using abs_tsum_sub_sum_Ioc_le hfg 0
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hN1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (Nat.one_le_floor_iff x).2 hx
  have hlogN : log ⌊x⌋₊ ≤ log x := log_le_log (by linarith) hNx
  have h1 := abs_sum_Ioc_mul_zeta_sub_le g hg ⌊x⌋₊
  have h2 : |(∑' d, g d / (d : ℝ)) * ⌊x⌋₊ - (∑' d, g d / (d : ℝ)) * x| ≤ 2 := by
    rw [← mul_sub, abs_mul]
    have : |(⌊x⌋₊ : ℝ) - x| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    nlinarith [abs_nonneg (∑' d, g d / (d : ℝ)), abs_nonneg ((⌊x⌋₊ : ℝ) - x)]
  calc _ ≤ (3 + log ⌊x⌋₊) + 2 := (abs_sub_le _ _ _).trans (add_le_add h1 h2)
    _ ≤ log x + 5 := by linarith

/-! ### The totient and divisor sums as Dirichlet convolutions -/

/-- `φ = μ * id`, as real-valued arithmetic functions. -/
theorem coe_moebius_mul_coe_id_apply (n : ℕ) :
    ((μ : ArithmeticFunction ℝ) * (ArithmeticFunction.id : ArithmeticFunction ℝ)) n
      = n.totient := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have key := (sum_eq_iff_sum_mul_moebius_eq (R := ℝ) (f := fun d => (d.totient : ℝ))
    (g := fun m => (m : ℝ))).mp (fun m _ => by exact_mod_cast Nat.sum_totient m) n hn
  rw [mul_apply]
  simpa using key

/-- `σ 1 = ζ * id`, as real-valued arithmetic functions. -/
theorem coe_zeta_mul_coe_id_apply (n : ℕ) :
    ((ζ : ArithmeticFunction ℝ) * (ArithmeticFunction.id : ArithmeticFunction ℝ)) n
      = σ 1 n := by
  rw [coe_zeta_mul_apply, sigma_one_apply]
  simp

/-- `φ(n) / n = ∑_{d ∣ n} μ(d) / d`, i.e. `φ / id = (μ / id) * ζ`. -/
theorem pdiv_coe_moebius_coe_id_mul_coe_zeta_apply (n : ℕ) :
    (pdiv (μ : ArithmeticFunction ℝ) (ArithmeticFunction.id : ArithmeticFunction ℝ) *
      (ζ : ArithmeticFunction ℝ)) n = (n.totient : ℝ) / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [coe_mul_zeta_apply, ← coe_moebius_mul_coe_id_apply, mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b =>
      (μ : ArithmeticFunction ℝ) a * (ArithmeticFunction.id : ArithmeticFunction ℝ) b), sum_div]
  refine sum_congr rfl fun d hd => ?_
  have hdn := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.pos_of_mem_divisors hd).ne'
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  simp only [pdiv_apply, natCoe_apply, id_apply, Nat.cast_div hdn hd0]
  field_simp

/-! ### Average orders -/

/-- `∑_{n ≤ x} φ(n) = (3 / π²) x² + O(x log x)`. -/
theorem _root_.Nat.sum_totient_sub_isBigO :
    (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, (n.totient : ℝ) - 3 / π ^ 2 * x ^ 2)
      =O[atTop] fun x => x * log x := by
  have hμ : ∀ n, |(μ : ArithmeticFunction ℝ) n| ≤ 1 := fun n => by
    rw [intCoe_apply]
    exact_mod_cast abs_moebius_le_one
  have hc : (∑' d, (μ : ArithmeticFunction ℝ) d / (d : ℝ) ^ 2) / 2 = 3 / π ^ 2 := by
    simp only [intCoe_apply]
    rw [tsum_moebius_div_sq]
    ring
  refine (sum_Ioc_mul_id_sub_isBigO _ hμ).congr_left fun x => ?_
  rw [hc, sum_congr rfl fun n _ => coe_moebius_mul_coe_id_apply n]

/-- **Mertens.** The average order of `φ(n)` is `(6 / π²) n`: `∑_{n ≤ x} φ(n) ~ (3 / π²) x²`. -/
theorem _root_.Nat.sum_totient_isEquivalent :
    (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, (n.totient : ℝ)) ~[atTop] fun x => 3 / π ^ 2 * x ^ 2 :=
  isEquivalent_of_sub_isBigO_mul_log (by positivity) Nat.sum_totient_sub_isBigO

/-- `∑_{n ≤ x} σ(n) = (π² / 12) x² + O(x log x)`. -/
theorem sum_sigma_one_sub_isBigO :
    (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 1 n : ℝ) - π ^ 2 / 12 * x ^ 2)
      =O[atTop] fun x => x * log x := by
  have hζ : ∀ n, |(ζ : ArithmeticFunction ℝ) n| ≤ 1 := fun n => by
    rw [natCoe_apply, zeta_apply]
    split_ifs <;> simp
  have hc : (∑' d, (ζ : ArithmeticFunction ℝ) d / (d : ℝ) ^ 2) / 2 = π ^ 2 / 12 := by
    have : ∀ d : ℕ, (ζ : ArithmeticFunction ℝ) d / (d : ℝ) ^ 2 = 1 / (d : ℝ) ^ 2 := fun d => by
      rcases eq_or_ne d 0 with rfl | hd
      · simp
      · simp [natCoe_apply, zeta_apply, hd]
    rw [tsum_congr this, hasSum_zeta_two.tsum_eq]
    ring
  refine (sum_Ioc_mul_id_sub_isBigO _ hζ).congr_left fun x => ?_
  rw [hc, sum_congr rfl fun n _ => coe_zeta_mul_coe_id_apply n]

/-- The average order of `σ(n)` is `(π² / 6) n`: `∑_{n ≤ x} σ(n) ~ (π² / 12) x²`. -/
theorem sum_sigma_one_isEquivalent :
    (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 1 n : ℝ)) ~[atTop] fun x => π ^ 2 / 12 * x ^ 2 :=
  isEquivalent_of_sub_isBigO_mul_log (by positivity) sum_sigma_one_sub_isBigO

/-- `∑_{n ≤ x} φ(n) / n = (6 / π²) x + O(log x)`, with the explicit bound
`|∑_{n ≤ x} φ(n) / n - (6 / π²) x| ≤ log x + 5` for `x ≥ 1`. -/
theorem _root_.Nat.abs_sum_totient_div_sub_le {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (n.totient : ℝ) / n - 6 / π ^ 2 * x| ≤ log x + 5 := by
  set g := pdiv (μ : ArithmeticFunction ℝ) (ArithmeticFunction.id : ArithmeticFunction ℝ)
  have hg : ∀ n, |g n| ≤ 1 / n := fun n => by
    simp only [g, pdiv_apply, intCoe_apply, natCoe_apply, id_apply, abs_div, Nat.abs_cast]
    gcongr
    exact_mod_cast abs_moebius_le_one
  have hc : ∑' d, g d / (d : ℝ) = 6 / π ^ 2 := by
    rw [← tsum_moebius_div_sq]
    refine tsum_congr fun d => ?_
    simp only [g, pdiv_apply, intCoe_apply, natCoe_apply, id_apply]
    ring
  have h := abs_sum_Ioc_floor_mul_zeta_sub_le g hg hx
  rwa [hc, sum_congr rfl fun n _ => pdiv_coe_moebius_coe_id_mul_coe_zeta_apply n] at h

/-- `∑_{n ≤ x} φ(n) / n = (6 / π²) x + O(log x)`. -/
theorem _root_.Nat.sum_totient_div_sub_isBigO :
    (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, (n.totient : ℝ) / n - 6 / π ^ 2 * x)
      =O[atTop] fun x => log x := by
  refine isBigO_iff.2 ⟨6, ?_⟩
  filter_upwards [eventually_ge_atTop (exp 1)] with x hx
  have hx1 : 1 ≤ x := le_trans (one_le_exp zero_le_one) hx
  have hlog : 1 ≤ log x := (le_log_iff_exp_le (by linarith)).2 hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ log x)]
  linarith [Nat.abs_sum_totient_div_sub_le hx1]

/-- **Dirichlet.** `|∑_{n ≤ x} d(n) - x log x| ≤ x` for `x ≥ 1`. -/
theorem abs_sum_sigma_zero_sub_mul_log_le {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ) - x * log x| ≤ x := by
  set N := ⌊x⌋₊ with hN
  have hx0 : (0 : ℝ) < x := by linarith
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_floor_iff x).2 hx
  have hS : ∑ n ∈ Ioc 0 N, (σ 0 n : ℝ) = ∑ d ∈ Ioc 0 N, ((N / d : ℕ) : ℝ) := by
    exact_mod_cast sum_Ioc_sigma0_eq_sum_div N
  have hH : ∑ d ∈ Ioc 0 N, (1 / (d : ℝ)) = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp only [one_div, Icc_one_eq_Ioc_zero]
  have hup : ∑ d ∈ Ioc 0 N, ((N / d : ℕ) : ℝ) ≤ x * (harmonic N : ℝ) := by
    rw [← hH, mul_sum]
    refine sum_le_sum fun d hd => ?_
    have hd : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.mp hd).1
    calc ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
      _ ≤ x / d := by gcongr
      _ = x * (1 / d) := by ring
  have hlo : x * (harmonic N : ℝ) - N ≤ ∑ d ∈ Ioc 0 N, ((N / d : ℕ) : ℝ) := by
    have hcard : ∑ d ∈ Ioc 0 N, (1 : ℝ) = N := by simp
    rw [← hH, mul_sum, ← hcard, ← sum_sub_distrib]
    refine sum_le_sum fun d hd => ?_
    have hd0 : 0 < d := (mem_Ioc.mp hd).1
    have hd : (0 : ℝ) < d := by exact_mod_cast hd0
    have h2 : (N : ℝ) + 1 ≤ d * (((N / d : ℕ) : ℝ) + 1) := by
      exact_mod_cast Nat.lt_mul_div_succ N hd0
    have h3 : x / d < ((N / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hd]
      nlinarith
    have : x * (1 / (d : ℝ)) = x / d := by ring
    linarith
  have hH1 : (harmonic N : ℝ) ≤ 1 + log N := harmonic_le_one_add_log N
  have hH2 : log ((N : ℝ) + 1) ≤ (harmonic N : ℝ) := by
    exact_mod_cast log_add_one_le_harmonic N
  have hlogN : log N ≤ log x := log_le_log (by positivity) hNx
  have hlogx : log x ≤ log ((N : ℝ) + 1) := log_le_log hx0 hxN.le
  rw [hS, abs_le]
  constructor <;> nlinarith

/-- **Dirichlet.** `∑_{n ≤ x} d(n) = x log x + O(x)`. -/
theorem sum_sigma_zero_sub_mul_log_isBigO :
    (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ) - x * log x) =O[atTop] fun x => x := by
  refine isBigO_iff.2 ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < x), one_mul]
  exact abs_sum_sigma_zero_sub_mul_log_le hx

end ArithmeticFunction

namespace Nat

open ArithmeticFunction

/-- **Sum of the integers up to `x` coprime to `k`.** For `k ≠ 0` and `x ≥ 0`,
`|∑_{n ≤ x, (n, k) = 1} n - φ(k) / (2k) · x²| ≤ 2 d(k) x`, where `d(k)` is the number of
divisors of `k`. -/
theorem abs_sum_coprime_sub_totient_div_mul_sq_le {k : ℕ} (hk0 : k ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊ with n.Coprime k, (n : ℝ) - (k.totient : ℝ) / (2 * k) * x ^ 2|
      ≤ 2 * #k.divisors * x := by
  change |(∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | Nat.Coprime n k}, (n : ℝ))
      - (k.totient : ℝ) / (2 * k) * x ^ 2| ≤ 2 * (k.divisors.card : ℝ) * x
  classical
  have gauss : ∀ M : ℕ, ∑ m ∈ Finset.Icc 1 M, (m : ℝ) = M * (M + 1) / 2 := fun M => by
    rw [Icc_one_eq_Ioc_zero]
    exact sum_Ioc_natCast M
  -- The sum of the multiples of `D` in `[1, N]`.
  have mult : ∀ D N : ℕ, 0 < D →
      (∑ n ∈ Finset.Icc 1 N, (if D ∣ n then (n : ℝ) else 0))
        = (D : ℝ) * (((N / D : ℕ) : ℝ) * (((N / D : ℕ) : ℝ) + 1) / 2) := by
    intro D N hD
    rw [← gauss (N / D), Finset.mul_sum, ← Finset.sum_filter]
    refine Finset.sum_nbij' (fun n => n / D) (fun m => D * m) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha
      obtain ⟨⟨h1, h2⟩, hd⟩ := ha
      simp only [Finset.mem_Icc]
      exact ⟨(Nat.one_le_div_iff hD).mpr (Nat.le_of_dvd (by omega) hd),
        Nat.div_le_div_right h2⟩
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ⟨m, rfl⟩⟩
      · nlinarith [hm.1, hD]
      · calc D * m ≤ D * (N / D) := Nat.mul_le_mul_left _ hm.2
          _ ≤ N := Nat.mul_div_le N D
    · intro a ha
      simp only [Finset.mem_filter] at ha
      exact Nat.mul_div_cancel' ha.2
    · intro m _
      exact Nat.mul_div_cancel_left m hD
    · intro a ha
      simp only [Finset.mem_filter] at ha
      have h2 : D * (a / D) = a := Nat.mul_div_cancel' ha.2
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h2.symm
  -- Replacing that sum by `N ^ 2 / (2 * D)` costs at most `N`.
  have tail : ∀ D N : ℕ, 0 < D →
      |(D : ℝ) * (((N / D : ℕ) : ℝ) * (((N / D : ℕ) : ℝ) + 1) / 2)
        - (N : ℝ) ^ 2 / (2 * (D : ℝ))| ≤ (N : ℝ) := by
    intro D N hD
    have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
    have hNr : (N : ℝ) = (D : ℝ) * ((N / D : ℕ) : ℝ) + ((N % D : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod N D).symm
    have hrlt : ((N % D : ℕ) : ℝ) < (D : ℝ) := by exact_mod_cast Nat.mod_lt N hD
    have hr0 : (0 : ℝ) ≤ ((N % D : ℕ) : ℝ) := Nat.cast_nonneg _
    have hm0 : (0 : ℝ) ≤ ((N / D : ℕ) : ℝ) := Nat.cast_nonneg _
    have key : (D : ℝ) * (((N / D : ℕ) : ℝ) * (((N / D : ℕ) : ℝ) + 1) / 2)
          - (N : ℝ) ^ 2 / (2 * (D : ℝ))
        = ((D : ℝ) ^ 2 * ((N / D : ℕ) : ℝ)
            - 2 * (D : ℝ) * ((N / D : ℕ) : ℝ) * ((N % D : ℕ) : ℝ)
            - ((N % D : ℕ) : ℝ) ^ 2) / (2 * (D : ℝ)) := by
      rw [hNr]; field_simp; ring
    rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (D : ℝ)),
      div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (D : ℝ)), hNr]
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
  have hNle : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx
  have hNgt : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
  -- Every subset of the prime factors of `k` has a positive product.
  have hDpos : ∀ s ∈ k.primeFactors.powerset, 0 < ∏ p ∈ s, p := by
    intro s hs
    rw [Finset.mem_powerset] at hs
    exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (hs hp)).pos
  -- Inclusion-exclusion over the prime factors of `k` detects coprimality.
  have incl : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊,
      (if Nat.Coprime n k then (n : ℝ) else 0)
        = ∑ s ∈ k.primeFactors.powerset,
            (-1 : ℝ) ^ s.card * (if (∏ p ∈ s, p) ∣ n then (n : ℝ) else 0) := by
    intro n hn
    have hn0 : n ≠ 0 := by
      simp only [Finset.mem_Icc] at hn; omega
    have hQP : k.primeFactors ∩ n.primeFactors ⊆ k.primeFactors := Finset.inter_subset_left
    have hiff : ∀ s ∈ k.primeFactors.powerset,
        ((∏ p ∈ s, p) ∣ n ↔ s ⊆ k.primeFactors ∩ n.primeFactors) := by
      intro s hs
      rw [Finset.mem_powerset] at hs
      constructor
      · intro hdvd p hp
        have hpP : p ∈ k.primeFactors := hs hp
        have hpd : p ∣ n := dvd_trans (Finset.dvd_prod_of_mem _ hp) hdvd
        exact Finset.mem_inter.mpr
          ⟨hpP, Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hpP, hpd, hn0⟩⟩
      · intro hsQ
        exact Finset.prod_primes_dvd n
          (fun a ha => (Nat.prime_of_mem_primeFactors (hs ha)).prime)
          (fun a ha => Nat.dvd_of_mem_primeFactors (Finset.mem_inter.mp (hsQ ha)).2)
    have step1 : (∑ s ∈ k.primeFactors.powerset,
          (-1 : ℝ) ^ s.card * (if (∏ p ∈ s, p) ∣ n then (n : ℝ) else 0))
        = (n : ℝ) * ∑ s ∈ k.primeFactors.powerset,
            (if s ⊆ k.primeFactors ∩ n.primeFactors then (-1 : ℝ) ^ s.card else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s hs => ?_
      by_cases h : (∏ p ∈ s, p) ∣ n
      · rw [ite_eq_left h, ite_eq_left ((hiff s hs).mp h)]; ring
      · rw [ite_eq_right h, ite_eq_right (fun hh => h ((hiff s hs).mpr hh))]; ring
    have step2 : (∑ s ∈ k.primeFactors.powerset,
          (if s ⊆ k.primeFactors ∩ n.primeFactors then (-1 : ℝ) ^ s.card else 0))
        = ∑ s ∈ (k.primeFactors ∩ n.primeFactors).powerset, (-1 : ℝ) ^ s.card := by
      rw [← Finset.sum_subset (Finset.powerset_mono.mpr hQP)]
      · exact Finset.sum_congr rfl fun s hs => ite_eq_left (Finset.mem_powerset.mp hs)
      · exact fun s _ hs2 => ite_eq_right (fun h => hs2 (Finset.mem_powerset.mpr h))
    have step3 : (∑ s ∈ (k.primeFactors ∩ n.primeFactors).powerset, (-1 : ℝ) ^ s.card)
        = if k.primeFactors ∩ n.primeFactors = ∅ then 1 else 0 := by
      by_cases hQe : k.primeFactors ∩ n.primeFactors = ∅
      · simp [hQe]
      · rw [ite_eq_right hQe]
        have h := Finset.sum_powerset_neg_one_pow_card (x := k.primeFactors ∩ n.primeFactors)
        rw [ite_eq_right hQe] at h
        exact_mod_cast congrArg (fun t : ℤ => (t : ℝ)) h
    have step4 : (k.primeFactors ∩ n.primeFactors = ∅) ↔ Nat.Coprime n k := by
      rw [← Finset.disjoint_iff_inter_eq_empty, Nat.disjoint_primeFactors hk0 hn0,
        Nat.coprime_comm]
    rw [step1, step2, step3]
    by_cases hc : Nat.Coprime n k
    · rw [ite_eq_left (step4.mpr hc), ite_eq_left hc, mul_one]
    · rw [ite_eq_right (fun h => hc (step4.mp h)), ite_eq_right hc, mul_zero]
  -- The coprime sum, expanded over the squarefree divisors of `k`.
  have hS : (∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | Nat.Coprime n k}, (n : ℝ))
      = ∑ s ∈ k.primeFactors.powerset, (-1 : ℝ) ^ s.card *
          (((∏ p ∈ s, p : ℕ) : ℝ) * ((((⌊x⌋₊ / ∏ p ∈ s, p : ℕ)) : ℝ) *
            ((((⌊x⌋₊ / ∏ p ∈ s, p : ℕ)) : ℝ) + 1) / 2)) := by
    rw [Finset.sum_filter, Finset.sum_congr rfl incl, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [← Finset.mul_sum, mult _ _ (hDpos s hs)]
  -- The main term.
  have hM : ∑ s ∈ k.primeFactors.powerset,
        (-1 : ℝ) ^ s.card * (((⌊x⌋₊ : ℕ) : ℝ) ^ 2 / (2 * ((∏ p ∈ s, p : ℕ) : ℝ)))
      = (k.totient : ℝ) / (2 * k) * ((⌊x⌋₊ : ℕ) : ℝ) ^ 2 := by
    have htot : (k.totient : ℝ) = (k : ℝ) * ∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹) := by
      have h2 := congrArg (fun t : ℚ => (t : ℝ)) (Nat.totient_eq_mul_prod_factors k)
      push_cast at h2
      exact h2
    have hexp : ∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹)
        = ∑ s ∈ k.primeFactors.powerset, (-1 : ℝ) ^ s.card * ((∏ p ∈ s, p : ℕ) : ℝ)⁻¹ := by
      have h := Finset.prod_add (fun p : ℕ => -((p : ℝ)⁻¹)) (fun _ : ℕ => (1 : ℝ)) k.primeFactors
      simp only [Finset.prod_const_one, mul_one] at h
      rw [show (∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹))
          = ∏ p ∈ k.primeFactors, (-((p : ℝ)⁻¹) + 1) from
        Finset.prod_congr rfl fun p _ => by ring]
      rw [h]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.prod_neg, Nat.cast_prod, ← Finset.prod_inv_distrib]
    have hterm : ∀ s ∈ k.primeFactors.powerset,
        (-1 : ℝ) ^ s.card * (((⌊x⌋₊ : ℕ) : ℝ) ^ 2 / (2 * ((∏ p ∈ s, p : ℕ) : ℝ)))
          = ((⌊x⌋₊ : ℕ) : ℝ) ^ 2 / 2 * ((-1 : ℝ) ^ s.card * ((∏ p ∈ s, p : ℕ) : ℝ)⁻¹) := by
      intro s _
      rw [← div_div, div_eq_mul_inv]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← hexp, htot]
    field_simp
  -- Comparing term by term.
  have hdiff : (∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | Nat.Coprime n k}, (n : ℝ))
      - (k.totient : ℝ) / (2 * k) * ((⌊x⌋₊ : ℕ) : ℝ) ^ 2
      = ∑ s ∈ k.primeFactors.powerset, (-1 : ℝ) ^ s.card *
          (((∏ p ∈ s, p : ℕ) : ℝ) * ((((⌊x⌋₊ / ∏ p ∈ s, p : ℕ)) : ℝ) *
              ((((⌊x⌋₊ / ∏ p ∈ s, p : ℕ)) : ℝ) + 1) / 2)
            - ((⌊x⌋₊ : ℕ) : ℝ) ^ 2 / (2 * ((∏ p ∈ s, p : ℕ) : ℝ))) := by
    rw [hS, ← hM, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  -- `2 ^ ω (k) ≤ d (k)`, by sending a set of primes to its product.
  have hcard : (k.primeFactors.powerset.card : ℝ) ≤ (k.divisors.card : ℝ) := by
    have h : k.primeFactors.powerset.card ≤ k.divisors.card := by
      refine Finset.card_le_card_of_injOn (fun s => ∏ p ∈ s, p) ?_ ?_
      · intro s hs
        rw [Finset.mem_coe, Finset.mem_powerset] at hs
        rw [Finset.mem_coe, Nat.mem_divisors]
        exact ⟨Finset.prod_primes_dvd k
          (fun a ha => (Nat.prime_of_mem_primeFactors (hs ha)).prime)
          (fun a ha => Nat.dvd_of_mem_primeFactors (hs ha)), hk0⟩
      · intro s hs t ht hst
        rw [Finset.mem_coe, Finset.mem_powerset] at hs ht
        rw [← Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (hs hp)),
          ← Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (ht hp))]
        exact congrArg Nat.primeFactors hst
    exact_mod_cast h
  have hbound1 : |(∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | Nat.Coprime n k}, (n : ℝ))
      - (k.totient : ℝ) / (2 * k) * ((⌊x⌋₊ : ℕ) : ℝ) ^ 2| ≤ (k.divisors.card : ℝ) * x := by
    rw [hdiff]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (g := fun _ => ((⌊x⌋₊ : ℕ) : ℝ)) (fun s hs => ?_)) ?_
    · rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact tail _ _ (hDpos s hs)
    · rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul hcard hNle (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hbound2 : |(k.totient : ℝ) / (2 * k) * ((⌊x⌋₊ : ℕ) : ℝ) ^ 2
      - (k.totient : ℝ) / (2 * k) * x ^ 2| ≤ x := by
    have htnn : (0 : ℝ) ≤ (k.totient : ℝ) / (2 * k) := by positivity
    have hthalf : (k.totient : ℝ) / (2 * k) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (k.totient : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.totient_le k
      linarith
    have habs2 : |((⌊x⌋₊ : ℕ) : ℝ) ^ 2 - x ^ 2| ≤ 2 * x := by
      have h1 : (0 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    calc |(k.totient : ℝ) / (2 * k) * ((⌊x⌋₊ : ℕ) : ℝ) ^ 2
            - (k.totient : ℝ) / (2 * k) * x ^ 2|
        = (k.totient : ℝ) / (2 * k) * |((⌊x⌋₊ : ℕ) : ℝ) ^ 2 - x ^ 2| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg htnn]
      _ ≤ 1 / 2 * (2 * x) := mul_le_mul hthalf habs2 (abs_nonneg _) (by norm_num)
      _ = x := by ring
  have hd1 : (1 : ℝ) ≤ (k.divisors.card : ℝ) := by
    have h : 0 < k.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk0⟩
    exact_mod_cast h
  calc |(∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | Nat.Coprime n k}, (n : ℝ))
          - (k.totient : ℝ) / (2 * k) * x ^ 2|
      ≤ |(∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | Nat.Coprime n k}, (n : ℝ))
            - (k.totient : ℝ) / (2 * k) * ((⌊x⌋₊ : ℕ) : ℝ) ^ 2|
        + |(k.totient : ℝ) / (2 * k) * ((⌊x⌋₊ : ℕ) : ℝ) ^ 2
            - (k.totient : ℝ) / (2 * k) * x ^ 2| := abs_sub_le _ _ _
    _ ≤ (k.divisors.card : ℝ) * x + x := by linarith
    _ ≤ 2 * (k.divisors.card : ℝ) * x := by nlinarith

end Nat
