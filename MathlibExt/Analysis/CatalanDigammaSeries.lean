/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import MathlibExt.Analysis.OddWeightedCatalanSeries
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A Catalan series in terms of the digamma function

We evaluate the Catalan series with a complex binomial denominator by telescoping
its sum with a multiple of the odd-weighted series at the shifted parameter.
-/

open Filter Finset Topology

namespace MetaMathlibExt
namespace tsum_catalan_div_four_pow_mul_binom

private noncomputable def binom (z : ℂ) (n : ℕ) : ℂ :=
  ∏ j ∈ Icc 1 n, (z + j) / j

private lemma binom_succ (z : ℂ) (n : ℕ) :
    binom z (n + 1) = binom z n * ((z + n + 1) / (n + 1)) := by
  simp only [binom, prod_Icc_succ_top (by omega : 1 ≤ n + 1), Nat.cast_succ, add_assoc]

private lemma add_nat_ne {z : ℂ} (hz : 0 < z.re) (n : ℕ) : z + n ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith [Nat.cast_nonneg (α := ℝ) n]

private lemma binom_ne {z : ℂ} (hz : 0 < z.re) (n : ℕ) : binom z n ≠ 0 :=
  prod_ne_zero_iff.mpr fun j hj ↦
    div_ne_zero (add_nat_ne hz j) (by exact_mod_cast (show 0 < j from (mem_Icc.mp hj).1).ne')

private lemma binom_shift (z : ℂ) (n : ℕ) :
    binom (z + 1) n * (z + 1) = binom z n * (z + n + 1) := by
  induction n with
  | zero => simp [binom]
  | succ n ih =>
    simp only [binom_succ, Nat.cast_succ]
    linear_combination ((z + n + 2) / (n + 1)) * ih

-- Multiplying the Catalan summand by n + 1 gives this telescoping coefficient.
private noncomputable def coeff (z : ℂ) (n : ℕ) : ℂ :=
  n.centralBinom / (4 ^ n * binom z n)

private lemma coeff_succ {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    coeff z (n + 1) = coeff z n * ((n + 1 / 2) / (z + n + 1)) := by
  have hr : ((n : ℂ) + 1) * (n + 1).centralBinom =
      2 * (2 * (n : ℂ) + 1) * n.centralBinom := by exact_mod_cast Nat.succ_mul_centralBinom_succ n
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hz' : z + n + 1 ≠ 0 := by simpa [add_assoc] using add_nat_ne hz (n + 1)
  simp only [coeff, binom_succ, pow_succ]
  field_simp [hn, hz', binom_ne hz]
  linear_combination 2 * hr

private lemma coeff_norm_step {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖coeff z (n + 1)‖ ≤ ‖coeff z n‖ * ((n + 1 / 2) / (n + 1)) := by
  have hden := Complex.re_le_norm (z + n + 1)
  simp only [Complex.add_re, Complex.natCast_re, Complex.one_re] at hden
  rw [coeff_succ hz, norm_mul, norm_div,
    show (n : ℂ) + 1 / 2 = ((n + 1 / 2 : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  gcongr
  linarith

private lemma coeff_norm_le {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖coeff z n‖ ≤ √(1 / (n + 1)) := by
  apply Real.le_sqrt_of_sq_le
  induction n with
  | zero => norm_num [coeff, binom]
  | succ n ih =>
    calc
      ‖coeff z (n + 1)‖ ^ 2 ≤ (‖coeff z n‖ * (((n : ℝ) + 1 / 2) / (n + 1))) ^ 2 := by
        gcongr
        exact coeff_norm_step hz n
      _ ≤ 1 / ((n : ℝ) + 1) * ((n + 1 / 2) / (n + 1)) ^ 2 := by rw [mul_pow]; gcongr
      _ ≤ _ := by
        rw [Nat.cast_succ]
        field_simp
        nlinarith [Nat.cast_nonneg (α := ℝ) n]

private lemma summable_div_succ {f : ℕ → ℂ} (hf : ∀ n : ℕ, ‖f n‖ ≤ √(1 / (n + 1))) :
    Summable fun n : ℕ ↦ f n / (n + 1) := by
  apply ((Real.summable_one_div_nat_add_rpow 1 (3 / 2)).mpr (by norm_num)).of_norm_bounded
  intro n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  rw [norm_div, ← Nat.cast_succ, Complex.norm_natCast, Nat.cast_succ, abs_of_pos hn,
    show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hn, Real.rpow_one,
    ← Real.sqrt_eq_rpow, ← div_div]
  exact div_le_div_of_nonneg_right (by simpa [Real.sqrt_div] using hf n) hn.le

private lemma catalan_term (z : ℂ) (n : ℕ) :
    (catalan n : ℂ) / (4 ^ n * binom z n) = coeff z n / (n + 1) := by
  have h : ((n : ℂ) + 1) * catalan n = n.centralBinom := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom n
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [coeff, ← h, div_right_comm, mul_div_cancel_left₀ _ hn]

private lemma weighted_term {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    (2 * (n : ℂ) + 1) * catalan n / (4 ^ n * binom (z + 1) n) =
      (2 * (z + 1)) * (coeff z (n + 1) / (n + 1)) := by
  have hc : ((n : ℂ) + 1) * catalan n = n.centralBinom := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom n
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hz' : z + n + 1 ≠ 0 := by simpa [add_assoc] using add_nat_ne hz (n + 1)
  rw [coeff_succ hz, coeff, ← hc]
  field_simp [hn, hz', binom_ne hz, binom_ne (z := z + 1) (by simp; linarith)]
  linear_combination -(2 * (n : ℂ) + 1) * (catalan n : ℂ) * binom_shift z n

private lemma term_telescope {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    coeff z n / (n + 1) + 2 * z * (coeff z (n + 1) / (n + 1)) =
      2 * (coeff z n - coeff z (n + 1)) := by
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hz' : z + n + 1 ≠ 0 := by simpa [add_assoc] using add_nat_ne hz (n + 1)
  rw [coeff_succ hz]
  field_simp [hn, hz']
  ring

end tsum_catalan_div_four_pow_mul_binom

open tsum_catalan_div_four_pow_mul_binom

/-- **A Catalan series in terms of the digamma function.** Let $z$ be a complex number with
$\operatorname{Re} z > 0$, let $\binom{n+z}{n} = \prod_{j=1}^{n} \frac{z + j}{j}$, let $C_n$ be the
$n$th Catalan number and $\psi$ the digamma function. Then
$$\sum_{n=0}^{\infty} \frac{C_n}{4^n \binom{n+z}{n}} =
-2z \bigl(\psi(z) - \psi(z + \tfrac12)\bigr).$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 3, identity (7) (`integers-2025-A18-thm-3`). -/
public theorem tsum_catalan_div_four_pow_mul_binom {z : ℂ} (hz : 0 < z.re) :
    ∑' n : ℕ, (catalan n : ℂ) / (4 ^ n * ∏ j ∈ Finset.Icc 1 n, (z + j) / j) =
      -2 * z * (Complex.digamma z - Complex.digamma (z + 1 / 2)) := by
  have hlim : Tendsto (coeff z) atTop (𝓝 0) :=
    squeeze_zero_norm (coeff_norm_le hz) (by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.sqrt)
  have hs := summable_div_succ (coeff_norm_le hz)
  have hs' := summable_div_succ (f := fun n ↦ coeff z (n + 1)) fun n ↦
    (coeff_norm_le hz (n + 1)).trans (by push_cast; gcongr; linarith)
  -- The partial sums telescope to twice the initial coefficient.
  have h := hs.hasSum.add (hs'.hasSum.mul_left (2 * z))
  simp_rw [term_telescope hz] at h
  have hpartial := h.tendsto_sum_nat
  simp_rw [← mul_sum, sum_range_sub'] at hpartial
  have hvalue := tendsto_nhds_unique hpartial
    (((tendsto_const_nhds (x := coeff z 0)).sub hlim).const_mul 2)
  -- The shifted odd-weighted series evaluates the second sum.
  have hw := tsum_odd_mul_catalan_div_four_pow_mul_binom (z := z + 1) (by simp; linarith)
  change ∑' n : ℕ, (2 * (n : ℂ) + 1) * catalan n / (4 ^ n * binom (z + 1) n) = _ at hw
  simp_rw [weighted_term hz] at hw
  have hp (m : ℕ) : z ≠ -m := fun e ↦ add_nat_ne hz m (by rw [e]; simp)
  have hz₁ : z + 1 ≠ 0 := by simpa using add_nat_ne hz 1
  rw [tsum_mul_left, mul_right_inj' (mul_ne_zero (by norm_num) hz₁),
    Complex.digamma_apply_add_one _ hp, show z + 1 - 1 / 2 = z + 1 / 2 by ring] at hw
  change ∑' n : ℕ, (catalan n : ℂ) / (4 ^ n * binom z n) = _
  simp_rw [catalan_term]
  rw [hw, show coeff z 0 = 1 by simp [coeff, binom], sub_zero, mul_one] at hvalue
  have hz₀ : z ≠ 0 := by simpa using add_nat_ne hz 0
  linear_combination hvalue - 2 * mul_inv_cancel₀ hz₀

end MetaMathlibExt
