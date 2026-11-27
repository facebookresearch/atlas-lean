/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import MathlibExt.Analysis.OddWeightedCatalanSeries
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Special values of Catalan series

The odd-weighted Catalan series at two and a telescoping difference give the sums with
numerator `catalan n` and denominators `4 ^ n * (n + 1)` and `4 ^ n * (n + 1) * (n + 2)`.
The corresponding sums with numerator `(2 * n + 1) * catalan n` specialize the digamma
identity at one and two.

## References

* Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of Nörlund*,
  INTEGERS 25 (2025), Article A18, pp. 1–12, Theorems 3 and 5 (in particular identity (11)).
  https://math.colgate.edu/~integers/z18/z18.pdf
-/

open Filter Finset Topology

namespace MetaMathlibExt

namespace CatalanSeriesSpecialValues

private noncomputable def coeff (n : ℕ) : ℝ := catalan n / (4 : ℝ) ^ n

private noncomputable def term (n : ℕ) : ℝ := coeff n / (n + 2)

private noncomputable def weighted (n : ℕ) : ℝ := (2 * n + 1) / (n + 1 : ℝ) * term n

private lemma coeff_tendsto : Tendsto coeff atTop (𝓝 0) := by
  apply squeeze_zero (fun n ↦ by unfold coeff; positivity) _
    tendsto_one_div_add_atTop_nhds_zero_nat
  intro n
  have h : ((n : ℝ) + 1) * catalan n ≤ 4 ^ n := by
    exact_mod_cast (succ_mul_catalan_eq_centralBinom n).le.trans (Nat.centralBinom_le_four_pow n)
  unfold coeff
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  linarith

-- The Catalan recurrence makes each term two thirds of a consecutive difference.
private lemma term_eq_sub (n : ℕ) : term n = (2 / 3) * (coeff n - coeff (n + 1)) := by
  have hc := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom n] at hc
  have hrec : (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n)
    simp only [Nat.succ_eq_add_one]
    linear_combination hc
  have h : ((n : ℝ) + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
    exact_mod_cast hrec
  unfold term coeff
  rw [pow_succ]
  field_simp
  linear_combination 2 * h

private lemma term_hasSum : HasSum term (2 / 3) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ by unfold term coeff; positivity) _).2
  simp_rw [term_eq_sub, ← mul_sum, sum_range_sub']
  simpa [coeff, catalan_zero] using
    ((tendsto_const_nhds (x := (1 : ℝ))).sub coeff_tendsto).const_mul (2 / 3)

private lemma binom_one (n : ℕ) :
    (∏ j ∈ Icc 1 n, (1 + j : ℂ) / j) = (n : ℂ) + 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [prod_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Nat.cast_succ]
    have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [mul_comm, div_mul_cancel₀ _ hn, add_comm 1]

private lemma binom_two (n : ℕ) :
    (∏ j ∈ Icc 1 n, (2 + j : ℂ) / j) = (n + 1) * (n + 2) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [prod_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Nat.cast_succ]
    have h : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp [h]
    ring

private lemma weighted_hasSum : HasSum weighted (4 * Real.log 2 - 2) := by
  have hsum : Summable weighted := by
    refine Summable.of_nonneg_of_le (fun n ↦ by unfold weighted term coeff; positivity)
      (fun n ↦ ?_) (term_hasSum.summable.mul_left 2)
    apply mul_le_mul_of_nonneg_right _ (by unfold term coeff; positivity)
    apply (div_le_iff₀ (by positivity)).2
    linarith
  apply hsum.hasSum_iff.mpr
  have h := tsum_odd_mul_catalan_div_four_pow_mul_binom (z := 2) (by norm_num)
  have hterm (n : ℕ) :
      (2 * (n : ℂ) + 1) * catalan n / (4 ^ n * ∏ j ∈ Icc 1 n, (2 + j : ℂ) / j) =
        2 * (weighted n : ℂ) := by
    rw [binom_two]
    unfold weighted term coeff
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  simp_rw [hterm] at h
  rw [tsum_mul_left, ← Complex.ofReal_tsum] at h
  have at_two := Complex.digamma_nat_add_one 1
  norm_num [harmonic] at at_two
  have half_shift := Complex.digamma_apply_add_one (1 / 2) (by
    intro m hm
    have := congrArg Complex.re hm
    norm_num at this
    linarith)
  rw [at_two, show (2 - 1 / 2 : ℂ) = 1 / 2 + 1 by norm_num, half_shift,
    Complex.digamma_one_half] at h
  apply Complex.ofReal_injective
  push_cast [-Complex.ofReal_tsum, Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  linear_combination h / 2

end CatalanSeriesSpecialValues

open CatalanSeriesSpecialValues

/-- **Catalan series summing to $4(1 - \log 2)$ and $\frac{10}{3} - 4 \log 2$.** With $C_n$ the
$n$th Catalan number,
$$\sum_{n=0}^{\infty} \frac{C_n}{4^n (n + 1)} = 4 (1 - \log 2)$$
and
$$\sum_{n=0}^{\infty} \frac{C_n}{4^n (n + 1)(n + 2)} = \frac{10}{3} - 4 \log 2.$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 3, first two identities
(`integers-2025-A18-thm-3`). -/
public theorem tsum_catalan_div_four_pow_special :
    ∑' n : ℕ, (catalan n : ℝ) / (4 ^ n * ((n : ℝ) + 1)) = 4 * (1 - Real.log 2) ∧
      ∑' n : ℕ, (catalan n : ℝ) / (4 ^ n * ((n : ℝ) + 1) * ((n : ℝ) + 2)) =
        10 / 3 - 4 * Real.log 2 := by
  constructor
  · have h := (term_hasSum.mul_left 3).sub weighted_hasSum
    convert h.tsum_eq using 1
    · apply tsum_congr
      intro n
      unfold weighted term coeff
      field_simp
      ring
    · ring
  · have h := (term_hasSum.mul_left 2).sub weighted_hasSum
    convert h.tsum_eq using 1
    · apply tsum_congr
      intro n
      unfold weighted term coeff
      field_simp
      ring
    · ring

/-- **Catalan series over powers of $4$ equal to $4\ln 2$ and $4\ln 2 - 2$.** Let $C_n$ be the
$n$-th Catalan number. Then
$$\sum_{n=0}^{\infty} \frac{2n+1}{n+1} \cdot \frac{C_n}{4^n} = 4\ln 2$$
and
$$\sum_{n=0}^{\infty} \frac{2n+1}{(n+1)(n+2)} \cdot \frac{C_n}{4^n} = 4\ln 2 - 2.$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 5, first two identities
(`integers-2025-A18-thm-5`). -/
public theorem tsum_odd_mul_catalan_div_four_pow_special :
    ∑' n : ℕ, (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) * catalan n / 4 ^ n = 4 * Real.log 2 ∧
      ∑' n : ℕ, (2 * (n : ℝ) + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) * catalan n / 4 ^ n =
        4 * Real.log 2 - 2 := by
  constructor
  · have h := tsum_odd_mul_catalan_div_four_pow_mul_binom (z := 1) (by norm_num)
    have hterm (n : ℕ) :
        (2 * (n : ℂ) + 1) * catalan n / (4 ^ n * ∏ j ∈ Icc 1 n, (1 + j : ℂ) / j) =
          Complex.ofReal ((2 * (n : ℝ) + 1) / ((n : ℝ) + 1) * catalan n / 4 ^ n) := by
      rw [binom_one]
      push_cast
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    simp_rw [hterm] at h
    rw [← Complex.ofReal_tsum] at h
    have at_one := Complex.digamma_nat_add_one 0
    norm_num [harmonic] at at_one
    rw [at_one, show (1 - 1 / 2 : ℂ) = 1 / 2 by norm_num, Complex.digamma_one_half] at h
    apply Complex.ofReal_injective
    push_cast [-Complex.ofReal_tsum, Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
    linear_combination h
  · convert weighted_hasSum.tsum_eq using 1
    apply tsum_congr
    intro n
    unfold weighted term coeff
    field_simp

end MetaMathlibExt
