/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.RingTheory.PowerSeries.Expand

import Mathlib.RingTheory.PowerSeries.Derivative
import MathlibExt.RingTheory.PowerSeries.SeriesDivisorInverseConvolution
import MathlibExt.RingTheory.PowerSeries.SeriesDivisorPowRecursion

/-!
# Calculus of series-divisors

A series-divisor recurrence is preserved, with the indicated transformations of its divisor
sequence, by inversion, substitution of `-q` or `q^m` for `q`, and natural powers.
-/

open PowerSeries

namespace MetaMathlibExt

/-- **Calculus of series-divisors.** Let $R$ be a commutative ring, let $A$ be a formal power
series over $R$, write $[q^k]F$ for the coefficient of $q^k$ in a power series $F$, and let
$s : \mathbb{N} \to R$ satisfy $n\,[q^n]A = \sum_{i=1}^{n} s(i)\,[q^{n-i}]A$ for every $n \ge 0$
(that is, $s$ is a series-divisor of $A$). Then the following hold for every $n \ge 0$:
(a) for every power series $B$ over $R$ with $AB = 1$,
$n\,[q^n]B = \sum_{i=1}^{n} \bigl(-s(i)\bigr)\,[q^{n-i}]B$;
(b) $n\,[q^n]A(-q) = \sum_{i=1}^{n} (-1)^i s(i)\,[q^{n-i}]A(-q)$;
(c) for every integer $m \ge 1$, $n\,[q^n]A(q^m) = \sum_{i=1}^{n} t_m(i)\,[q^{n-i}]A(q^m)$,
where $t_m(i) = m\,s(i/m)$ if $m \mid i$ and $t_m(i) = 0$ otherwise;
(d) for every integer $m \ge 0$, $n\,[q^n]A^m = \sum_{i=1}^{n} m\,s(i)\,[q^{n-i}]A^m$.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Proposition 3
(`jis-2024-24.1.6-prop-3`). -/
public theorem series_divisor_calculus {R : Type*} [CommRing R]
    (A : PowerSeries R) (s : ℕ → R)
    (hA : ∀ n : ℕ, (n : R) * coeff n A = ∑ i ∈ Finset.Icc 1 n, s i * coeff (n - i) A) :
    (∀ B : PowerSeries R, A * B = 1 → ∀ n : ℕ,
      (n : R) * coeff n B = ∑ i ∈ Finset.Icc 1 n, -s i * coeff (n - i) B) ∧
    (∀ n : ℕ, (n : R) * coeff n (rescale (-1) A) =
      ∑ i ∈ Finset.Icc 1 n, (-1) ^ i * s i * coeff (n - i) (rescale (-1) A)) ∧
    (∀ (m : ℕ) (hm : m ≠ 0) (n : ℕ), (n : R) * coeff n (expand m hm A) =
      ∑ i ∈ Finset.Icc 1 n,
        (if m ∣ i then (m : R) * s (i / m) else 0) * coeff (n - i) (expand m hm A)) ∧
    (∀ m n : ℕ, (n : R) * coeff n (A ^ m) =
      ∑ i ∈ Finset.Icc 1 n, (m : R) * s i * coeff (n - i) (A ^ m)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B hAB n
    -- The recurrence ignores `s 0`; normalize it for the inverse convolution identity.
    let t (i : ℕ) := if i = 0 then 0 else s i
    have ht0 : t 0 = 0 := by simp [t]
    have ht_pos (i : ℕ) (hi : 1 ≤ i) : t i = s i := by simp [t, Nat.ne_zero_of_lt hi]
    have ht (k : ℕ) : (k : R) * coeff k A = ∑ i ∈ Finset.Icc 1 k, t i * coeff (k - i) A := by
      rw [hA]
      exact Finset.sum_congr rfl fun i hi ↦ by rw [ht_pos i (Finset.mem_Icc.mp hi).1]
    let D : Derivation R (PowerSeries R) (PowerSeries R) := (X : PowerSeries R) • derivative
    have coeffD (F : PowerSeries R) (k : ℕ) : coeff k (D F) = (k : R) * coeff k F := by
      change coeff k (X * derivative F) = _
      cases k with
      | zero => simp
      | succ k => rw [coeff_succ_X_mul, coeff_derivative, Nat.cast_succ, mul_comm]
    have hS : B * D A = PowerSeries.mk t := by
      ext k
      rw [coeff_mk, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simpa only [coeffD, mul_comm (coeff _ B)] using
        (series_divisor_inverse_convolution A B hAB t ht0 ht k).1.symm
    have hDB : D B = -(PowerSeries.mk t * B) := by
      have h := congrArg D hAB
      rw [D.leibniz, D.map_one_eq_zero, smul_eq_mul, smul_eq_mul, hS] at h
      have h' : A * D B = -PowerSeries.mk t := eq_neg_of_add_eq_zero_left h
      calc
        D B = B * (A * D B) := by rw [← mul_assoc, mul_comm B A, hAB, one_mul]
        _ = -(PowerSeries.mk t * B) := by rw [h', mul_neg, mul_comm B]
    rw [← coeffD, hDB, map_neg, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_eq_add_Ico _ (Nat.succ_pos n), Nat.succ_eq_add_one,
      Finset.Ico_add_one_right_eq_Icc]
    simp only [coeff_mk, ht0, zero_mul, zero_add, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [← neg_mul, ht_pos i (Finset.mem_Icc.mp hi).1]
  · intro n
    simp only [coeff_rescale]
    rw [mul_left_comm, hA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hsign : (-1 : R) ^ n = (-1) ^ i * (-1) ^ (n - i) := by
      rw [← pow_add, Nat.add_sub_of_le (Finset.mem_Icc.mp hi).2]
    rw [hsign]
    ac_rfl
  · intro m hm n
    by_cases hmn : m ∣ n
    · obtain ⟨k, rfl⟩ := hmn
      have hmpos := Nat.pos_of_ne_zero hm
      rw [coeff_expand_mul, Nat.cast_mul, mul_assoc, hA, Finset.mul_sum]
      calc
        _ = ∑ i ∈ (Finset.Icc 1 (m * k)).filter (m ∣ ·),
            (m : R) * s (i / m) * coeff (m * k - i) (expand m hm A) := by
          refine Finset.sum_bij (fun j _ ↦ m * j) ?_ ?_ ?_ ?_
          · intro j hj
            obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hj
            exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
              ⟨Nat.mul_pos hmpos hj1, Nat.mul_le_mul_left m hjk⟩, dvd_mul_right m j⟩
          · intro a _ b _ hab
            exact Nat.eq_of_mul_eq_mul_left hmpos hab
          · intro i hi
            obtain ⟨hi, j, rfl⟩ := Finset.mem_filter.mp hi
            obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hi
            refine ⟨j, Finset.mem_Icc.mpr ⟨?_, (Nat.mul_le_mul_left_iff hmpos).mp hjk⟩, rfl⟩
            exact Nat.pos_of_ne_zero fun h ↦ by simp [h] at hj1
          · intro j _
            rw [Nat.mul_div_cancel_left _ hmpos, ← Nat.mul_sub_left_distrib, coeff_expand_mul,
              mul_assoc]
        _ = _ := by simp only [Finset.sum_filter, ite_mul, zero_mul]
    · rw [coeff_expand_of_not_dvd m hm A hmn, mul_zero]
      symm
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      by_cases hmi : m ∣ i
      · have hsub : ¬ m ∣ n - i := fun h ↦
          hmn (Nat.sub_add_cancel (Finset.mem_Icc.mp hi).2 ▸ dvd_add h hmi)
        rw [coeff_expand_of_not_dvd m hm A hsub, mul_zero]
      · simp [hmi]
  · intro m n
    simpa only [Finset.mul_sum, mul_assoc] using series_divisor_pow_recursion A s hA m n

end MetaMathlibExt
