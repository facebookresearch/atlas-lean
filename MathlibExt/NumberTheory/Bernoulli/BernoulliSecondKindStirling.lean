/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.NumberTheory.Bernoulli.BernoulliSecondKind
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.PowerSeries.Log
import MathlibExt.Combinatorics.Enumerative.StirlingSecondExplicit

/-!
# Bernoulli numbers in terms of Bernoulli numbers of the second kind

The theorem `bernoulli_eq_neg_sum` expresses each positive-index Bernoulli number as a
weighted sum of Bernoulli numbers of the second kind using Stirling numbers of the second kind.
-/

namespace MathlibExt.NumberTheory.BernoulliSecondKindWanted

open PowerSeries MetaMathlibExt

-- Expand the power by the binomial theorem and apply the explicit Stirling sum.
private theorem coeff_exp_sub_one_pow (n k : ℕ) :
    coeff n ((exp ℚ - 1) ^ k) =
      (Nat.stirlingSecond n k : ℚ) * k.factorial / n.factorial := by
  have h : (Nat.stirlingSecond n k : ℚ) * k.factorial =
      ∑ j ∈ Finset.range (k + 1), (-1 : ℚ) ^ (k - j) * k.choose j * (j : ℚ) ^ n := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact stirlingSecond_mul_factorial_eq_sum n k
  rw [show exp ℚ - 1 = exp ℚ + C (-1 : ℚ) by simp [sub_eq_add_neg],
    add_pow, map_sum, h, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_mul_natCast, ← map_pow, coeff_mul_C, exp_pow_eq_rescale_exp, coeff_rescale, coeff_exp]
  simp
  ring

-- For E = exp(X) - 1 and G the second-kind series, (log(1+X)/X)(E) is the ordinary
-- Bernoulli series B. The identity G * (log(1+X)/X) = 1 then gives X * ((G-1)/X)(E) = 1-B.
private theorem subst_shift_bernoulliSecond :
    X * (mk fun k => coeff (k + 1) bernoulliSecondPowerSeries).subst (exp ℚ - 1) =
      1 - bernoulliPowerSeries ℚ := by
  let L := mk fun n : ℕ => (-1 : ℚ) ^ n / (n + 1)
  let E := exp ℚ - 1
  let σ : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ := substAlgHom HasSubst.exp_sub_one
  have hlog : X * L = log ℚ := by
    ext n
    cases n with
    | zero => simp
    | succ n => simp [L, coeff_succ_X_mul, pow_succ]
  have hXL : E * σ L = X := by
    calc
      E * σ L = σ (X * L) := by rw [map_mul, substAlgHom_X]
      _ = X := by simp only [hlog, σ, coe_substAlgHom, subst_log_exp_sub_one]
  have hE : E ≠ 0 := by
    intro h
    have := congrArg (coeff 1) h
    norm_num [E, coeff_exp] at this
  have hB : σ L = bernoulliPowerSeries ℚ := by
    apply mul_left_cancel₀ hE
    rw [hXL, mul_comm E, bernoulliPowerSeries_mul_exp_sub_one]
  have hG : constantCoeff bernoulliSecondPowerSeries = 1 := by
    simp [bernoulliSecondPowerSeries, constantCoeff_inv]
  have hshift := congrArg σ (sub_const_eq_X_mul_shift bernoulliSecondPowerSeries)
  rw [hG, map_one, map_sub, map_one, map_mul, substAlgHom_X] at hshift
  have hprod := congrArg σ bernoulliSecondPowerSeries_mul_mk
  change σ (bernoulliSecondPowerSeries * L) = σ 1 at hprod
  rw [map_mul, map_one] at hprod
  rw [← coe_substAlgHom HasSubst.exp_sub_one]
  change X * σ _ = 1 - bernoulliPowerSeries ℚ
  rw [← hXL, mul_right_comm E, ← hshift, sub_mul, hprod, one_mul, hB]

/-- **Bernoulli numbers in terms of Bernoulli numbers of the second kind.** Let $B_m$ be the
Bernoulli numbers (with $B_1 = -1/2$), $B_m^*$ the Bernoulli numbers of the second kind and
$S(m, j)$ the Stirling numbers of the second kind. For every natural number $n \ge 1$,
$$B_n = -\sum_{k=1}^{n} \frac{n}{k} \, S(n-1, k-1) \, B_k^*.$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Corollary 2. -/
public theorem bernoulli_eq_neg_sum (n : ℕ) (hn : 1 ≤ n) :
    bernoulli n =
      -∑ k ∈ Finset.Icc 1 n, (n : ℚ) / k *
        (Nat.stirlingSecond (n - 1) (k - 1) : ℚ) *
        MetaMathlibExt.bernoulliSecond k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h := congrArg (coeff (m + 1)) subst_shift_bernoulliSecond
  rw [coeff_succ_X_mul, coeff_subst' HasSubst.exp_sub_one] at h
  simp only [coeff_mk, smul_eq_mul, coeff_exp_sub_one_pow, map_sub, coeff_one,
    Nat.succ_ne_zero, ite_false, zero_sub, bernoulliPowerSeries, Algebra.algebraMap_self,
    RingHom.id_apply] at h
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (m + 1))] at h
  · rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.succ_sub_one, Nat.add_comm 1]
    have hm := neg_eq_iff_eq_neg.mp h.symm
    rw [div_eq_iff (by positivity)] at hm
    rw [hm, neg_mul, neg_inj, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [bernoulliSecond_eq, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
  · intro k hk
    by_contra! hout
    have hlt : m < k := by simpa using hout
    exact hk (by simp [Nat.stirlingSecond_eq_zero_of_lt hlt])

end MathlibExt.NumberTheory.BernoulliSecondKindWanted
