/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown

@[expose] public section

namespace MetaMathlibExt

/-! # Ordinary generating function of the binomial transform
-/

open scoped BigOperators

/-- **Generating function of the binomial transform over a field.** Let $K$ be a field and let
$a : \mathbb{N} \to K$ be a sequence with ordinary generating function
$A(X) = \sum_n a_n X^n \in K[[X]]$. Then the ordinary generating function of the binomial
transform $n \mapsto \sum_{k=0}^{n} \binom{n}{k} a_k$ of $a$ equals
$(1 - X)^{-1} \cdot A\big(X (1 - X)^{-1}\big)$ in $K[[X]]$, where $A\big(X (1 - X)^{-1}\big)$ is
the power series obtained by substituting $X (1 - X)^{-1}$ for $X$ in $A$. -/
theorem mk_sum_choose_mul_eq_inv_one_sub_mul_subst {K : Type*} [Field K]
    (a : ℕ → K) :
    PowerSeries.mk
        (fun n : ℕ =>
          ∑ k ∈ Finset.range (n + 1), (n.choose k : K) * a k) =
      (1 - (PowerSeries.X : PowerSeries K))⁻¹ *
        (PowerSeries.mk a).subst
          ((PowerSeries.X : PowerSeries K) * (1 - PowerSeries.X)⁻¹) := by
  set u : PowerSeries K := (1 - PowerSeries.X)⁻¹ with hu_def
  set b : PowerSeries K := PowerSeries.X * u with hb_def
  have hconst : PowerSeries.constantCoeff (1 - PowerSeries.X : PowerSeries K) ≠ 0 := by
    simp [PowerSeries.constantCoeff_X]
  have hconst' : MvPowerSeries.constantCoeff (1 - PowerSeries.X : PowerSeries K) ≠ 0 := by
    rw [← PowerSeries.constantCoeff_eq]
    exact hconst
  have hu : u = PowerSeries.mk 1 := by
    rw [hu_def, MvPowerSeries.inv_eq_iff_mul_eq_one hconst']
    exact PowerSeries.mk_one_mul_one_sub_eq_one K
  have hcancel : u * (1 - PowerSeries.X) = 1 := by
    rw [hu_def]
    exact MvPowerSeries.inv_mul_cancel _ hconst'
  have hb : PowerSeries.HasSubst b := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    rw [hb_def]
    simp [PowerSeries.constantCoeff_X]
  have hpas : ∀ m k : ℕ, ((m + 1).choose (k + 1) : K) =
      (m.choose k : K) + (m.choose (k + 1) : K) := by
    intro m k
    have h := Nat.choose_succ_succ m k
    simp only [Nat.succ_eq_add_one] at h
    rw [h, Nat.cast_add]
  have eX : ∀ (m : ℕ) (f : PowerSeries K),
      PowerSeries.coeff (m + 1) (PowerSeries.X * f) = PowerSeries.coeff m f := by
    intro m f
    rw [show (PowerSeries.X : PowerSeries K) = PowerSeries.X ^ 1 from (pow_one _).symm,
      PowerSeries.coeff_X_pow_mul]
  have eX0 : ∀ f : PowerSeries K, PowerSeries.coeff 0 (PowerSeries.X * f) = 0 := by
    intro f
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_X,
      zero_mul]
  have hpow : ∀ d : ℕ, b ^ d = PowerSeries.X ^ d * u ^ d := by
    intro d
    rw [hb_def, mul_pow]
  have hvanish : ∀ n d : ℕ, n < d → PowerSeries.coeff n (b ^ d) = 0 := by
    intro n d hnd
    have hdd : n + (d - n) = d := by omega
    have hfacX : (PowerSeries.X : PowerSeries K) ^ d =
        PowerSeries.X ^ n * PowerSeries.X ^ (d - n) := by
      rw [← pow_add, hdd]
    have hmain : PowerSeries.coeff n
        (PowerSeries.X ^ n * (PowerSeries.X ^ (d - n) * u ^ d)) =
        PowerSeries.coeff 0 (PowerSeries.X ^ (d - n) * u ^ d) := by
      have h := PowerSeries.coeff_X_pow_mul (PowerSeries.X ^ (d - n) * u ^ d) n 0
      rwa [zero_add] at h
    rw [hpow d, hfacX, mul_assoc, hmain,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow,
      PowerSeries.constantCoeff_X, zero_pow (by omega : d - n ≠ 0), zero_mul]
  have hmatch : ∀ m d : ℕ, d ≤ m →
      PowerSeries.coeff (m + 1) (b ^ (d + 1)) = (m.choose d : K) := by
    intro m d hdm
    have h2 : d + (m - d) = m := by omega
    have e1 : m + 1 = (m - d) + (d + 1) := by omega
    rw [hpow, e1, PowerSeries.coeff_X_pow_mul, hu,
      PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_mk, h2]
  have hsupp : ∀ n : ℕ, Function.support (fun d => a d * PowerSeries.coeff n (b ^ d)) ⊆
      ↑(Finset.range (n + 1)) := by
    intro n d hd
    rw [Function.mem_support] at hd
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hlt
    exact hd (by rw [hvanish n d (by omega), mul_zero])
  have hS : ∀ n : ℕ, PowerSeries.coeff n ((PowerSeries.mk a).subst b) =
      ∑ d ∈ Finset.range (n + 1), a d * PowerSeries.coeff n (b ^ d) := by
    intro n
    have hfib : (fun d => PowerSeries.coeff d (PowerSeries.mk a) • PowerSeries.coeff n (b ^ d)) =
        (fun d => a d * PowerSeries.coeff n (b ^ d)) := by
      funext d
      simp [PowerSeries.coeff_mk]
    rw [PowerSeries.coeff_subst' hb, hfib, finsum_eq_sum_of_support_subset _ (hsupp n)]
  have hL : ∀ m : ℕ,
      (∑ k ∈ Finset.range (m + 1 + 1), ((m + 1).choose k : K) * a k) -
      (∑ k ∈ Finset.range (m + 1), (m.choose k : K) * a k) =
      (∑ k ∈ Finset.range (m + 1), (m.choose k : K) * a (k + 1)) := by
    intro m
    have peel1 : (∑ k ∈ Finset.range (m + 1 + 1), ((m + 1).choose k : K) * a k) =
        (∑ k ∈ Finset.range (m + 1), ((m + 1).choose (k + 1) : K) * a (k + 1)) +
        (((m + 1).choose 0 : ℕ) : K) * a 0 :=
      Finset.sum_range_succ' _ _
    have peel2 : (∑ k ∈ Finset.range (m + 1), (m.choose k : K) * a k) =
        (∑ k ∈ Finset.range m, (m.choose (k + 1) : K) * a (k + 1)) +
        ((m.choose 0 : ℕ) : K) * a 0 :=
      Finset.sum_range_succ' _ _
    rw [peel1, peel2]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, add_sub_add_right_eq_sub]
    have hhm : (m.choose (m + 1) : K) * a (m + 1) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (by omega : m < m + 1), Nat.cast_zero, zero_mul]
    have hext : (∑ k ∈ Finset.range m, (m.choose (k + 1) : K) * a (k + 1)) =
        (∑ k ∈ Finset.range (m + 1), (m.choose (k + 1) : K) * a (k + 1)) := by
      have pe : (∑ k ∈ Finset.range (m + 1), (m.choose (k + 1) : K) * a (k + 1)) =
          (∑ k ∈ Finset.range m, (m.choose (k + 1) : K) * a (k + 1)) +
          (m.choose (m + 1) : K) * a (m + 1) :=
        Finset.sum_range_succ _ _
      rw [pe, hhm, add_zero]
    rw [hext]
    have hcomb : (∑ k ∈ Finset.range (m + 1),
          (((m + 1).choose (k + 1) : K) * a (k + 1) -
            (m.choose (k + 1) : K) * a (k + 1))) =
        (∑ k ∈ Finset.range (m + 1), ((m + 1).choose (k + 1) : K) * a (k + 1)) -
        (∑ k ∈ Finset.range (m + 1), (m.choose (k + 1) : K) * a (k + 1)) :=
      Finset.sum_sub_distrib _ _
    rw [← hcomb]
    have hsplit : (∑ k ∈ Finset.range (m + 1),
          (((m + 1).choose (k + 1) : K) * a (k + 1) -
            (m.choose (k + 1) : K) * a (k + 1))) =
        (∑ k ∈ Finset.range m,
          (((m + 1).choose (k + 1) : K) * a (k + 1) -
            (m.choose (k + 1) : K) * a (k + 1))) +
        (((m + 1).choose (m + 1) : K) * a (m + 1) -
          (m.choose (m + 1) : K) * a (m + 1)) :=
      Finset.sum_range_succ _ _
    have hRHS : (∑ k ∈ Finset.range (m + 1), (m.choose k : K) * a (k + 1)) =
        (∑ k ∈ Finset.range m, (m.choose k : K) * a (k + 1)) +
        (m.choose m : K) * a (m + 1) :=
      Finset.sum_range_succ _ _
    rw [hsplit, hRHS, hhm, sub_zero]
    congr 1
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hpas m k]
      ring
    · simp [Nat.choose_self]
  have hSb : ∀ m : ℕ,
      (∑ d ∈ Finset.range (m + 1 + 1), a d * PowerSeries.coeff (m + 1) (b ^ d)) =
      (∑ k ∈ Finset.range (m + 1), a (k + 1) * (m.choose k : K)) := by
    intro m
    have peel : (∑ d ∈ Finset.range (m + 1 + 1), a d * PowerSeries.coeff (m + 1) (b ^ d)) =
        (∑ d ∈ Finset.range (m + 1), a (d + 1) * PowerSeries.coeff (m + 1) (b ^ (d + 1))) +
        a 0 * PowerSeries.coeff (m + 1) (b ^ 0) :=
      Finset.sum_range_succ' _ _
    rw [peel]
    have hz : a 0 * PowerSeries.coeff (m + 1) (b ^ 0) = 0 := by
      rw [pow_zero, PowerSeries.coeff_one, ite_eq_right (by omega), mul_zero]
    rw [hz, add_zero]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Finset.mem_range] at hd
    rw [hmatch m d (by omega)]
  have key : (1 - PowerSeries.X) * PowerSeries.mk
      (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℕ) : K) * a k) =
      (PowerSeries.mk a).subst b := by
    apply PowerSeries.ext
    intro n
    simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_mk]
    by_cases hn : n = 0
    · subst hn
      have e1 : (∑ k ∈ Finset.range (0 + 1), ((((0).choose k : ℕ)) : K) * a k) = a 0 := by
        rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, Nat.choose_self, Nat.cast_one,
          one_mul]
      have e3 : (∑ d ∈ Finset.range (0 + 1), a d * PowerSeries.coeff 0 (b ^ d)) = a 0 := by
        rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, pow_zero,
          PowerSeries.coeff_one, ite_eq_left rfl, mul_one]
      rw [hS 0, e1, eX0, e3, sub_zero]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simp only [Nat.succ_eq_add_one]
      rw [eX m, PowerSeries.coeff_mk, hS (m + 1), hL m, hSb m]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact mul_comm _ _
  have hfin := congrArg (u * ·) key
  rw [← mul_assoc, hcancel, one_mul] at hfin
  exact hfin

/--
**Ordinary generating function of the binomial transform.** Let $a : \mathbb{N} \to \mathbb{R}$
be a real sequence with ordinary generating function $A(X) = \sum_n a_n X^n \in \mathbb{R}[[X]]$.
Then the ordinary generating function of the binomial transform
$n \mapsto \sum_{k=0}^{n} \binom{n}{k} a_k$ of $a$ equals
$(1 - X)^{-1} \cdot A\big(X (1 - X)^{-1}\big)$ in $\mathbb{R}[[X]]$, where
$A\big(X (1 - X)^{-1}\big)$ is the power series obtained by substituting $X (1 - X)^{-1}$ for $X$
in $A$.

Proves `Wanted` entry `ordinary_generating_function_binomial_transform`.

Source: Ayhan Dil, Veli Kurt, and Mehmet Cenkci,
"Algorithms for Bernoulli and Related Polynomials,"
Journal of Integer Sequences 10 (2007), Article 07.5.4,
Proposition (label prop1), lines 205–218 (proof attributed to Euler there).
`https://cs.uwaterloo.ca/journals/JIS/VOL10/Dil/dil11.tex`
It is the case `K = ℝ` of `mk_sum_choose_mul_eq_inv_one_sub_mul_subst`.
-/
theorem ordinary_generating_function_binomial_transform
    (a : ℕ → ℝ) :
    PowerSeries.mk
        (fun n : ℕ =>
          ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a k) =
      (1 - (PowerSeries.X : PowerSeries ℝ))⁻¹ *
        (PowerSeries.mk a).subst
          ((PowerSeries.X : PowerSeries ℝ) * (1 - PowerSeries.X)⁻¹) :=
  mk_sum_choose_mul_eq_inv_one_sub_mul_subst a

end MetaMathlibExt
