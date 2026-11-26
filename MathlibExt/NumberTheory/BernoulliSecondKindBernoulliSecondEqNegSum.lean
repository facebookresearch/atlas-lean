/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.RingTheory.PowerSeries.Log
public import MathlibExt.Combinatorics.Enumerative.SignedStirlingFirst
public import MathlibExt.NumberTheory.Bernoulli.BernoulliSecondKindStirling
public import MathlibExt.NumberTheory.Bernoulli.BernoulliStirlingSum
public import MathlibExt.NumberTheory.Bernoulli.WeightedStirlingSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Bernoulli numbers of the second kind in terms of Bernoulli numbers

The theorem `bernoulliSecond_eq_neg_sum` expresses each positive-index Bernoulli number of
the second kind as a weighted sum of Bernoulli numbers using signed Stirling numbers of the
first kind.

Statements from Bakir Farhi, "Formulas Involving Bernoulli
and Stirling Numbers of Both Kinds", *Journal of Integer
Sequences* 28 (2025), Article 25.2.6
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Farhi/farhi26.tex>).
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.BernoulliSecondKindWanted

open PowerSeries MetaMathlibExt

-- Derivative of a power of `log` times `1 + X`.
private theorem deriv_log_pow_mul (k : ℕ) :
    d⁄dX ((log ℚ) ^ (k + 1)) * (1 + X) = (((k + 1 : ℕ)) : ℚ⟦X⟧) * (log ℚ) ^ k := by
  have hderiv : d⁄dX ((log ℚ) ^ (k + 1))
      = (((k + 1 : ℕ)) : ℚ⟦X⟧) * (log ℚ) ^ (k + 1 - 1) * d⁄dX (log ℚ) := by
    have h := derivative_pow (log ℚ) (k + 1)
    simpa using h
  rw [hderiv]
  have hlog := derivative_log_mul_one_add_X (A := ℚ)
  have hsub : k + 1 - 1 = k := by omega
  rw [hsub]
  calc ((((k + 1 : ℕ)) : ℚ⟦X⟧) * (log ℚ) ^ k * d⁄dX (log ℚ)) * (1 + X)
      = ((((k + 1 : ℕ)) : ℚ⟦X⟧) * (log ℚ) ^ k) * (d⁄dX (log ℚ) * (1 + X)) := by ring
    _ = ((((k + 1 : ℕ)) : ℚ⟦X⟧) * (log ℚ) ^ k) * 1 := by rw [hlog]
    _ = (((k + 1 : ℕ)) : ℚ⟦X⟧) * (log ℚ) ^ k := by ring

-- Coefficients of `f' * (1 + X)` in terms of coefficients of `f`.
private theorem coeff_deriv_mul_one_add (f : ℚ⟦X⟧) (n : ℕ) :
    coeff n (d⁄dX f * (1 + X)) = (n + 1 : ℚ) * coeff (n + 1) f + (n : ℚ) * coeff n f := by
  have hmul : d⁄dX f * (1 + X) = d⁄dX f + X * d⁄dX f := by ring
  rw [hmul, map_add, coeff_derivative]
  cases n with
  | zero =>
    rw [coeff_zero_X_mul]
    simp
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

-- Coefficient recurrence for powers of `log` from the derivative identity.
private theorem coeff_log_pow_succ (k n : ℕ) :
    (n + 1 : ℚ) * coeff (n + 1) ((log ℚ) ^ (k + 1)) + (n : ℚ) * coeff n ((log ℚ) ^ (k + 1))
      = (k + 1 : ℚ) * coeff n ((log ℚ) ^ k) := by
  have h := congrArg (coeff n) (deriv_log_pow_mul k)
  rw [coeff_deriv_mul_one_add, coeff_natCast_mul] at h
  push_cast at h ⊢
  linarith [h]

-- Base case `k = 0` for the coefficient formula.
private theorem coeff_log_pow_zero (n : ℕ) :
    coeff n ((log ℚ) ^ (0 : ℕ))
      = (signedStirlingFirst n 0 : ℚ) * (0 : ℕ).factorial / n.factorial := by
  simp only [pow_zero]
  cases n with
  | zero => simp
  | succ n => simp

-- Base case `n = 0` for positive powers.
private theorem coeff_log_pow_zero_succ (k : ℕ) :
    coeff 0 ((log ℚ) ^ (k + 1))
      = (signedStirlingFirst 0 (k + 1) : ℚ) * ((k + 1 : ℕ).factorial : ℚ)
        / (0 : ℕ).factorial := by
  have hconst : coeff 0 ((log ℚ) ^ (k + 1)) = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_log]
    simp
  have hs : signedStirlingFirst 0 (k + 1) = 0 :=
    signedStirlingFirst_eq_zero_of_lt (Nat.zero_lt_succ k)
  rw [hconst, hs]
  simp

-- Coefficients of powers of `log` via signed Stirling numbers of the first kind.
private theorem coeff_log_pow (n k : ℕ) :
    coeff n ((log ℚ) ^ k)
      = (signedStirlingFirst n k : ℚ) * (k.factorial : ℚ) / (n.factorial : ℚ) := by
  induction k generalizing n with
  | zero => exact coeff_log_pow_zero n
  | succ k ih =>
    induction n with
    | zero => exact coeff_log_pow_zero_succ k
    | succ n ihn =>
      have hrel := coeff_log_pow_succ k n
      have hk := ih n
      have hn := ihn
      have hstir : (signedStirlingFirst (n + 1) (k + 1) : ℚ)
          = (signedStirlingFirst n k : ℚ) - (n : ℚ) * (signedStirlingFirst n (k + 1) : ℚ) := by
        have h := signedStirlingFirst_succ_succ n k
        exact_mod_cast h
      have h1 : coeff (n + 1) ((log ℚ) ^ (k + 1))
          = ((k + 1 : ℚ) * coeff n ((log ℚ) ^ k) - (n : ℚ) * coeff n ((log ℚ) ^ (k + 1)))
            / (n + 1 : ℚ) := by
        have h2 : (n + 1 : ℚ) * coeff (n + 1) ((log ℚ) ^ (k + 1))
            = (k + 1 : ℚ) * coeff n ((log ℚ) ^ k) - (n : ℚ) * coeff n ((log ℚ) ^ (k + 1)) := by
          linarith [hrel]
        rw [eq_div_iff (by positivity : (n + 1 : ℚ) ≠ 0)]
        linarith [h2]
      rw [h1, hk, hn]
      rw [hstir]
      have hfk : (((k + 1 : ℕ)).factorial : ℚ) = (k + 1 : ℚ) * (k.factorial : ℚ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hfn : (((n + 1 : ℕ)).factorial : ℚ) = (n + 1 : ℚ) * (n.factorial : ℚ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hfk, hfn]
      field_simp

-- For `F = log(1+X)` and `G` the second-kind series, `X * ((B-1)/X)(F) = 1 - G`.
private theorem subst_shift_bernoulli :
    X * (mk fun k => coeff (k + 1) (bernoulliPowerSeries ℚ)).subst (log ℚ) =
      1 - bernoulliSecondPowerSeries := by
  let L := mk fun n : ℕ => (-1 : ℚ) ^ n / (n + 1)
  let F := log ℚ
  let E := exp ℚ - 1
  let B := bernoulliPowerSeries ℚ
  let G := bernoulliSecondPowerSeries
  let σ : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ := substAlgHom HasSubst.log
  have hlog : X * L = F := by
    ext n
    cases n with
    | zero => simp [L, F]
    | succ n => simp [L, F, coeff_succ_X_mul, pow_succ, coeff_log]
  have hE : σ E = X := by
    have hexp : σ (exp ℚ) = 1 + X := by
      have h := subst_exp_log ℚ
      rw [← coe_substAlgHom HasSubst.log] at h
      simpa [σ] using h
    simp only [E, σ, map_sub, map_one] at *
    rw [hexp]
    ring
  have hX : σ X = F := substAlgHom_X HasSubst.log
  have hB_mul : B * E = X := bernoulliPowerSeries_mul_exp_sub_one ℚ
  have htau : σ B * X = F := by
    have h := congrArg σ hB_mul
    rw [map_mul, hE, hX] at h
    exact h
  have hτB : σ B = L := by
    have hXL : X * L = F := hlog
    have h : σ B * X = X * L := by rw [htau, hXL]
    rw [mul_comm (σ B) X] at h
    exact mul_left_cancel₀ X_ne_zero h
  have hBconst : constantCoeff B = 1 := by
    simp [B, bernoulliPowerSeries, constantCoeff_mk, bernoulli_zero]
  have hshift := congrArg σ (sub_const_eq_X_mul_shift B)
  rw [hBconst, map_one, map_sub, map_one, map_mul, hX] at hshift
  have hshift_tau : σ B - 1 = F * σ (mk fun k => coeff (k + 1) B) := hshift
  have hGF : G * F = X := by
    have hG : G * L = 1 := bernoulliSecondPowerSeries_mul_mk
    calc G * F = G * (X * L) := by rw [hlog]
      _ = X * (G * L) := by ring
      _ = X := by rw [hG, mul_one]
  have hFshift : F * σ (mk fun k => coeff (k + 1) B) = L - 1 := by
    have h : σ B - 1 = F * σ (mk fun k => coeff (k + 1) B) := hshift_tau
    rw [hτB] at h
    exact h.symm
  have hgoal : X * σ (mk fun k => coeff (k + 1) B) = 1 - G := by
    calc X * σ (mk fun k => coeff (k + 1) B)
        = (G * F) * σ (mk fun k => coeff (k + 1) B) := by rw [hGF]
      _ = G * (F * σ (mk fun k => coeff (k + 1) B)) := by ring
      _ = G * (L - 1) := by rw [hFshift]
      _ = 1 - G := by
        have hG : G * L = 1 := bernoulliSecondPowerSeries_mul_mk
        calc G * (L - 1) = G * L - G := by ring
          _ = 1 - G := by rw [hG]
  rw [← coe_substAlgHom HasSubst.log]
  change X * σ _ = 1 - G
  exact hgoal

/-- **Bernoulli numbers of the second kind in terms of Bernoulli numbers.** Let $B_m$ be the
Bernoulli numbers (with $B_1 = -1/2$), $B_m^*$ the Bernoulli numbers of the second kind and
$s(m, j)$ the signed Stirling numbers of the first kind. For every natural number $n \ge 1$,
$$B_n^* = -\sum_{k=1}^{n} \frac{n}{k} \, s(n-1, k-1) \, B_k.$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Theorem 4. -/
public theorem bernoulliSecond_eq_neg_sum (n : ℕ)
    (hn : 1 ≤ n) :
    MetaMathlibExt.bernoulliSecond n =
      -∑ k ∈ Finset.Icc 1 n, (n : ℚ) / k *
        (MetaMathlibExt.signedStirlingFirst (n - 1) (k - 1) : ℚ) * bernoulli k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h := congrArg (coeff (m + 1)) subst_shift_bernoulli
  rw [coeff_succ_X_mul, coeff_subst' HasSubst.log] at h
  simp only [coeff_mk, smul_eq_mul, coeff_log_pow, map_sub, coeff_one,
    Nat.succ_ne_zero, ite_false, zero_sub, bernoulliPowerSeries,
    Algebra.algebraMap_self, RingHom.id_apply] at h
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (m + 1))] at h
  · rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.succ_sub_one, Nat.add_comm 1]
    have hG : coeff (m + 1) bernoulliSecondPowerSeries
        = bernoulliSecond (m + 1) / (((m + 1 : ℕ)).factorial : ℚ) := by
      rw [bernoulliSecond_eq]
      field_simp
    rw [hG] at h
    have hm := neg_eq_iff_eq_neg.mp h.symm
    rw [div_eq_iff (by positivity)] at hm
    rw [hm, neg_mul, neg_inj, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra hcon
    have hlt : m < k := by omega
    exact hk (by simp [signedStirlingFirst_eq_zero_of_lt hlt])

end MathlibExt.NumberTheory.BernoulliSecondKindWanted
