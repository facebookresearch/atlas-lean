/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPowerSeries_pderiv_subst.lean`
and
`P2M/Sol/S_MvPowerSeries_pderiv_subst.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution

@[expose] public section

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

private theorem pderiv_pow_succ (i : σ) (a : MvPowerSeries σ R) (n : ℕ) :
    MvPowerSeries.pderiv i (a ^ (n + 1)) =
      ((n + 1 : ℕ) : MvPowerSeries σ R) * a ^ n * MvPowerSeries.pderiv i a := by
  rw [MvPowerSeries.pderiv_pow, Nat.add_sub_cancel]

private theorem coeff_pow_eq_zero (a : MvPowerSeries σ R)
    (ha : MvPowerSeries.constantCoeff a = 0) {e : σ →₀ ℕ} {n : ℕ}
    (h : e.degree < n) : MvPowerSeries.coeff e (a ^ n) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast h)
    (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n ha)

private theorem coeff_pow_mul_eq_zero (a b : MvPowerSeries σ R)
    (ha : MvPowerSeries.constantCoeff a = 0) {e : σ →₀ ℕ} {n : ℕ}
    (h : e.degree < n) : MvPowerSeries.coeff e (a ^ n * b) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_ MvPowerSeries.le_order_mul
  exact lt_of_lt_of_le
    (lt_of_lt_of_le (by exact_mod_cast h)
      (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n ha)) le_self_add

private theorem coeff_subst_eq_sum (a : MvPowerSeries σ R)
    (ha : MvPowerSeries.constantCoeff a = 0) (h : PowerSeries R)
    (e : σ →₀ ℕ) (N : ℕ) (hN : e.degree < N) :
    MvPowerSeries.coeff e (PowerSeries.subst a h) =
      ∑ n ∈ Finset.range N, PowerSeries.coeff n h • MvPowerSeries.coeff e (a ^ n) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  apply finsum_eq_sum_of_support_subset
  intro n hn
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  apply hn
  simp only
  rw [coeff_pow_eq_zero a ha (lt_of_lt_of_le hN (not_lt.mp hlt)), smul_zero]

/-- Chain rule for substituting a multivariate power series with zero constant
term into a univariate power series: differentiating the composite with respect
to a variable `i` gives the composite of the derivative times the derivative of
the substituted series. -/
public theorem pderiv_subst {σ : Type*} {R : Type*} [CommRing R] (i : σ)
    (a : MvPowerSeries σ R) (ha : MvPowerSeries.constantCoeff a = 0)
    (h : PowerSeries R) :
    MvPowerSeries.pderiv i (PowerSeries.subst a h) =
      PowerSeries.subst a (PowerSeries.derivative (R := R) h) *
        MvPowerSeries.pderiv i a := by
  classical
  ext d
  set K := d.degree + 1 with hK
  have hdeg1 : (d + Finsupp.single i 1).degree = d.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have hne : d + Finsupp.single i 1 ≠ 0 := by
    intro h0
    have := congrArg (fun e => e i) h0
    simp at this
  have e1 : ∀ m : ℕ, MvPowerSeries.coeff (d + Finsupp.single i 1) (a ^ (m + 1)) *
        ((d i : R) + 1)
      = ((m + 1 : ℕ) : R) * MvPowerSeries.coeff d (a ^ m * MvPowerSeries.pderiv i a) := by
    intro m
    rw [← MvPowerSeries.coeff_pderiv, pderiv_pow_succ, mul_assoc,
      ← map_natCast (MvPowerSeries.C (σ := σ) (R := R)), MvPowerSeries.coeff_C_mul]
  have hL : MvPowerSeries.coeff d (MvPowerSeries.pderiv i (PowerSeries.subst a h))
      = ∑ m ∈ Finset.range K, (PowerSeries.coeff (m + 1) h * (m + 1)) •
          MvPowerSeries.coeff d (a ^ m * MvPowerSeries.pderiv i a) := by
    rw [MvPowerSeries.coeff_pderiv,
      coeff_subst_eq_sum a ha h (d + Finsupp.single i 1) (K + 1)
        (by rw [hdeg1, hK]; omega),
      Finset.sum_mul, Finset.sum_range_succ']
    simp only [pow_zero, MvPowerSeries.coeff_one, ite_eq_right hne, smul_zero, zero_mul,
      add_zero]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_mul_assoc, e1, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  have hin : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal d,
      MvPowerSeries.coeff x.1 (PowerSeries.subst a (PowerSeries.derivative (R := R) h))
        * MvPowerSeries.coeff x.2 (MvPowerSeries.pderiv i a)
      = ∑ m ∈ Finset.range (K + 1), PowerSeries.coeff m (PowerSeries.derivative (R := R) h)
          • (MvPowerSeries.coeff x.1 (a ^ m) *
            MvPowerSeries.coeff x.2 (MvPowerSeries.pderiv i a)) := by
    intro x hx
    have hxd : (x.1 : σ →₀ ℕ).degree ≤ d.degree := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rw [← hx, map_add]; omega
    rw [coeff_subst_eq_sum a ha _ x.1 (K + 1) (by rw [hK]; omega), Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_mul_assoc]
  have hR : MvPowerSeries.coeff d
        (PowerSeries.subst a (PowerSeries.derivative (R := R) h) * MvPowerSeries.pderiv i a)
      = ∑ m ∈ Finset.range K, (PowerSeries.coeff (m + 1) h * (m + 1)) •
          MvPowerSeries.coeff d (a ^ m * MvPowerSeries.pderiv i a) := by
    rw [MvPowerSeries.coeff_mul, Finset.sum_congr rfl hin, Finset.sum_comm]
    simp only [← Finset.smul_sum, ← MvPowerSeries.coeff_mul]
    rw [Finset.sum_range_succ,
      coeff_pow_mul_eq_zero a _ ha (show d.degree < K by rw [hK]; omega), smul_zero,
      add_zero]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [PowerSeries.coeff_derivative]
  rw [hL, hR]

end MvPowerSeries
