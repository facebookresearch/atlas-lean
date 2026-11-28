/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition

import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.Partition.OverpartitionCongruence
import MathlibExt.RingTheory.PowerSeries.SeriesDivisorCalculus
import MathlibExt.RingTheory.PowerSeries.SeriesDivisorInverseConvolution
import MathlibExt.RingTheory.PowerSeries.SeriesDivisorProduct

/-!
# Overpartitions and Glaisher's divisor sum with odd cofactors

For every natural number `n`, two convolutions of the overpartition numbers (with signed
square shifts) give the divisor sum with odd cofactors and its self-convolution. The product
formula gives the series-divisor of the overpartition generating function. Its reciprocal
is the signed square theta series, so only squares survive in the inverse convolutions.

## References

* Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite Products*,
  Journal of Integer Sequences **27** (2024), Article 24.1.6, Theorem 26, p. 16;
  see also Theorem 9, Lemma 25, and equations (5) and (16).
* George E. Andrews, Richard Askey, and Ranjan Roy, *Special Functions*, Encyclopedia of
  Mathematics and its Applications **71**, Cambridge University Press (1999), p. 500
  (the pentagonal number theorem and Gauss's specialization of the Jacobi triple product).
* `MathlibExt.RingTheory.PowerSeries.SeriesDivisorProduct`,
  `MetaMathlibExt.series_divisor_add_of_mul`: the coefficient form of the derivative used
  for the factor `1 - X`.
-/

open Finset Filter PowerSeries
open scoped ArithmeticFunction.sigma

namespace MetaMathlibExt

local notation "σ₁" m:max => ((σ 1 m : ℕ) : ℤ)
local notation "σdiv" k:max m:max => (if k ∣ m then ((σ 1 (m / k) : ℕ) : ℤ) else 0)
local notation "dD" m:max => ∑ d ∈ Nat.divisors m with Odd (m / d), (d : ℤ)
local notation "pbar" m:max => ((Nat.card (Nat.Overpartition m) : ℕ) : ℤ)
local notation "overpartitionSeries" => (Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ)))
local notation "signedTheta" => (rescale (-1 : ℤ) squareThetaSeries)

private lemma oddCofactorSum (n : ℕ) : (dD n) = σ₁ n - σdiv 2 n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hsum := sum_filter_add_sum_filter_not n.divisors (fun d ↦ Odd (n / d)) (fun d ↦ (d : ℤ))
  rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum]
  have hEven : (∑ d ∈ n.divisors with ¬ Odd (n / d), (d : ℤ)) = σdiv 2 n := by
    by_cases hn₂ : 2 ∣ n
    · rw [ite_eq_left hn₂, ArithmeticFunction.sigma_one_apply, Nat.cast_sum]
      have hdiv := Nat.div_dvd_of_dvd hn₂
      rw [← Nat.divisors_filter_dvd_of_dvd hn hdiv]
      congr 1
      apply filter_congr
      intro d hd
      have hdvd := Nat.dvd_of_mem_divisors hd
      rw [Nat.not_odd_iff_even, even_iff_two_dvd, Nat.dvd_div_iff_mul_dvd hdvd,
        Nat.dvd_div_iff_mul_dvd hn₂, mul_comm d 2]
    · rw [ite_eq_right hn₂, sum_eq_zero]
      intro d hd
      obtain ⟨hd, he⟩ := mem_filter.mp hd
      have h₂ : 2 ∣ n / d := (Nat.not_odd_iff_even.mp he).two_dvd
      exact (hn₂ (h₂.trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))).elim
  rw [← hEven, ← hsum, add_sub_cancel_right]

private lemma seriesDivisor_one_sub_X (n : ℕ) :
    (n : ℤ) * coeff n (1 - X : ℤ⟦X⟧) =
      ∑ i ∈ Icc 1 n, (-1 : ℤ) * coeff (n - i) (1 - X : ℤ⟦X⟧) := by
  let S : ℤ⟦X⟧ := PowerSeries.mk fun _ ↦ -1
  have hS : derivative (1 - X : ℤ⟦X⟧) = S * (1 - X) := by
    rw [map_sub, derivative_one, derivative_X, zero_sub, mul_sub, mul_one]
    ext k
    cases k with
    | zero => simp [S]
    | succ k => simp [S, coeff_succ_mul_X, coeff_one]
  cases n with
  | zero => simp
  | succ k =>
    have h := congrArg (coeff k) hS
    rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    simpa [S, Nat.add_comm 1, mul_comm (coeff _ _), Nat.cast_succ] using h

private lemma seriesDivisor_pentagonal (n : ℕ) :
    (n : ℤ) * coeff n (pentagonalSeries ℤ) =
      ∑ i ∈ Icc 1 n, -(σ₁ i) * coeff (n - i) (pentagonalSeries ℤ) := by
  let P (s : Finset ℕ) : ℤ⟦X⟧ := ∏ j ∈ s, (1 - X ^ (j + 1))
  let w (j i : ℕ) : ℤ := if j + 1 ∣ i then -(↑(j + 1) : ℤ) else 0
  have hfactor (j k : ℕ) : (k : ℤ) * coeff k (1 - X ^ (j + 1) : ℤ⟦X⟧) =
      ∑ i ∈ Icc 1 k, w j i * coeff (k - i) (1 - X ^ (j + 1) : ℤ⟦X⟧) := by
    simpa [w, expand_X, mul_neg_one] using
      (series_divisor_calculus (1 - X : ℤ⟦X⟧) (fun _ ↦ -1) seriesDivisor_one_sub_X).2.2.1
        (j + 1) (Nat.succ_ne_zero j) k
  have hprod (s : Finset ℕ) (k : ℕ) : (k : ℤ) * coeff k (P s) =
      ∑ i ∈ Icc 1 k, (∑ j ∈ s, w j i) * coeff (k - i) (P s) := by
    induction s using Finset.induction_on generalizing k with
    | empty => cases k <;> simp [P, coeff_one]
    | @insert j s hjs ih =>
      simpa only [P, prod_insert hjs, sum_insert hjs] using
        series_divisor_add_of_mul _ _ (w j) (fun i ↦ ∑ a ∈ s, w a i) (hfactor j) ih k
  have hev : ∀ᶠ s : Finset ℕ in atTop, ∀ k ∈ range (n + 1),
      coeff k (P s) = coeff k (pentagonalSeries ℤ) := by
    exact (eventually_all_finset _).mpr fun k _ ↦ coeff_prod_one_sub_X_pow_eventually_eq ℤ k
  obtain ⟨s, hs, hcoeff⟩ := ((eventually_ge_atTop (range n)).and hev).exists
  have hsum (i : ℕ) (hi : i ∈ Icc 1 n) : (∑ j ∈ s, w j i) = -(σ₁ i) := by
    obtain ⟨hip, hin⟩ := mem_Icc.mp hi
    rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum, ← sum_neg_distrib]
    simp only [w, ← sum_filter]
    refine sum_bij (fun j _ ↦ j + 1) ?_ ?_ ?_ (fun _ _ ↦ rfl)
    · intro j hj
      exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hj).2, Nat.ne_zero_of_lt hip⟩
    · intro a _ b _ h
      omega
    · intro d hd
      have hd₁ := Nat.pos_of_mem_divisors hd
      have hdn := (Nat.divisor_le hd).trans hin
      refine ⟨d - 1, mem_filter.mpr ⟨hs (mem_range.mpr (by omega)), ?_⟩, by omega⟩
      simpa [Nat.sub_add_cancel hd₁] using Nat.dvd_of_mem_divisors hd
  rw [← hcoeff n (mem_range.mpr (Nat.lt_succ_self n)), hprod]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [hsum i hi, hcoeff (n - i) (mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le ..)))]

private lemma seriesDivisor_overpartition (n : ℕ) :
    (n : ℤ) * coeff n overpartitionSeries =
      ∑ i ∈ Icc 1 n, 2 * (dD i) * coeff (n - i) overpartitionSeries := by
  let E := pentagonalSeries ℤ
  have hE : constantCoeff E = 1 := by
    have h0 : pentagonal 0 = 0 := by rw [pentagonal_def]; decide
    rw [← coeff_zero_eq_constantCoeff_apply, ← h0]
    change coeff (pentagonal 0) (pentagonalSeries ℤ) = 1
    rw [coeff_pentagonalSeries_pentagonal]
    simp
  have hUnit : IsUnit E := isUnit_iff_constantCoeff.mpr (by rw [hE]; exact isUnit_one)
  have hU := hUnit.pow 2
  let V : ℤ⟦X⟧ := ↑hU.unit⁻¹
  have hUV : E ^ 2 * V = 1 := hU.unit.mul_inv_of_eq hU.unit_spec
  have hquot : expand 2 two_ne_zero E * V = overpartitionSeries := by
    rw [← overpartition_genFun_mul_pentagonalSeries_sq, mul_assoc, hUV, mul_one]
  have hcalc := series_divisor_calculus E (fun i ↦ -(σ₁ i)) seriesDivisor_pentagonal
  have hV := (series_divisor_calculus (E ^ 2) (fun i ↦ (2 : ℤ) * -(σ₁ i))
    (hcalc.2.2.2 2)).1 V hUV
  have h := series_divisor_add_of_mul _ _ _ _ (hcalc.2.2.1 2 two_ne_zero) hV n
  rw [hquot] at h
  refine h.trans (sum_congr rfl fun i _ ↦ ?_)
  rw [oddCofactorSum]
  congr 1
  by_cases hi : 2 ∣ i <;> simp only [hi, ite_true, ite_false] <;> ring

private lemma sum_mul_signedTheta (n : ℕ) (f : ℕ → ℤ) :
    (∑ j ∈ Icc 1 n, f j * coeff j signedTheta) =
      2 * ∑ i ∈ Icc 1 n with i ^ 2 ≤ n, (-1) ^ i * f (i ^ 2) := by
  let T := (Icc 1 n).filter fun i ↦ i ^ 2 ≤ n
  have hset : ((Icc 1 n).filter fun j ↦ j ∈ (Icc 1 j).image (fun i ↦ i ^ 2)) =
      T.image (fun i ↦ i ^ 2) := by
    ext j
    simp only [T, mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨_, hjn⟩, i, ⟨hi, hij⟩, rfl⟩
      exact ⟨i, ⟨⟨hi, hij.trans hjn⟩, hjn⟩, rfl⟩
    · rintro ⟨i, ⟨⟨hi, _⟩, hisq⟩, rfl⟩
      have hle : i ≤ i ^ 2 := Nat.le_self_pow (by decide) i
      exact ⟨⟨hi.trans hle, hisq⟩, i, ⟨hi, hle⟩, rfl⟩
  calc
    _ = ∑ j ∈ (Icc 1 n).filter (fun j ↦ j ∈ (Icc 1 j).image (fun i ↦ i ^ 2)),
        2 * ((-1 : ℤ) ^ j * f j) := by
      rw [sum_filter]
      refine sum_congr rfl fun j hj ↦ ?_
      rw [coeff_rescale, coeff_squareThetaSeries,
        ite_eq_right (Nat.ne_zero_of_lt (mem_Icc.mp hj).1)]
      split_ifs <;> ring
    _ = _ := by
      rw [hset, sum_image (fun a _ b _ h ↦ Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) h),
        mul_sum]
      refine sum_congr rfl fun i _ ↦ ?_
      have hsign : (-1 : ℤ) ^ (i ^ 2) = (-1) ^ i := by
        rcases Nat.even_or_odd i with he | ho
        · have hsq : Even (i ^ 2) := by simpa [pow_two] using he.mul_right i
          rw [hsq.neg_one_pow, he.neg_one_pow]
        · have hsq : Odd (i ^ 2) := by simpa [pow_two] using ho.mul ho
          rw [hsq.neg_one_pow, ho.neg_one_pow]
      rw [hsign]

/-- **Overpartition formulas for a divisor sum with odd cofactors.** Let $n$ be a natural number.
Write $\sigma(m)$ for the sum of the positive divisors of $m$, $\sigma(m/2)$ for $\sigma$
evaluated at $m/2$ when $m$ is even and for $0$ when $m$ is odd, and $d_D(m)$ for the sum of the
divisors $d$ of $m$ with $m/d$ odd, with $\sigma(0) = d_D(0) = 0$; let $\bar p(m)$ be the number
of overpartitions of $m$. Then $2 d_D(n) = 2(\sigma(n) - \sigma(n/2)) = n\,\bar p(n) +
2\sum_{i \ge 1,\ i^2 \le n} (-1)^i (n - i^2)\,\bar p(n - i^2)$ and
$2\sum_{i=1}^{n} d_D(n-i)\,d_D(i) =
\sum_{i \ge 1,\ i^2 \le n} (-1)^{i+1} i^2 (n - i^2)\,\bar p(n - i^2)$.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 26
(`jis-2024-24.1.6-thm-26`). -/
public theorem overpartition_glaisher_dD_formulas (n : ℕ) :
    (2 * (dD n) = 2 * ((σ₁ n) - σdiv 2 n) ∧
      2 * ((σ₁ n) - σdiv 2 n) = (n : ℤ) * pbar n +
        2 * ∑ i ∈ Finset.Icc 1 n with i ^ 2 ≤ n,
          (-1) ^ i * ((n : ℤ) - (i : ℤ) ^ 2) * pbar (n - i ^ 2)) ∧
    2 * ∑ i ∈ Finset.Icc 1 n, (dD (n - i)) * dD i =
      ∑ i ∈ Finset.Icc 1 n with i ^ 2 ≤ n,
        (-1) ^ (i + 1) * (i : ℤ) ^ 2 * ((n : ℤ) - (i : ℤ) ^ 2) * pbar (n - i ^ 2) := by
  have hInv : overpartitionSeries * signedTheta = 1 := by
    simpa [rescale_rescale, mul_comm] using
      congrArg (rescale (-1 : ℤ)) overpartitionOdd_square_recurrence.theta_mul_rescale_genFun
  have h := series_divisor_inverse_convolution overpartitionSeries signedTheta hInv
    (fun i ↦ 2 * (dD i)) (by simp) seriesDivisor_overpartition n
  have hPos : (∑ i ∈ Icc 1 n, ((n - i : ℕ) : ℤ) * coeff (n - i) overpartitionSeries *
        coeff i signedTheta) =
      2 * ∑ i ∈ Icc 1 n with i ^ 2 ≤ n,
        (-1) ^ i * ((n : ℤ) - (i : ℤ) ^ 2) * pbar (n - i ^ 2) := by
    rw [sum_mul_signedTheta]
    congr 1
    refine sum_congr rfl fun i hi ↦ ?_
    rw [Nat.cast_sub (mem_filter.mp hi).2, Nat.cast_pow, ← overpartition_card_eq_coeff_genFun,
      mul_assoc]
  have hFirst := h.1
  rw [sum_range_eq_add_Ico _ (Nat.succ_pos n), Nat.succ_eq_add_one, Ico_add_one_right_eq_Icc,
    Nat.sub_zero, coeff_rescale, pow_zero, one_mul, coeff_squareThetaSeries_small.1, mul_one,
    hPos, ← overpartition_card_eq_coeff_genFun] at hFirst
  have hdd : 2 * (dD n) = 2 * ((σ₁ n) - σdiv 2 n) := by rw [oddCofactorSum]
  refine ⟨⟨hdd, hdd.symm.trans hFirst⟩, ?_⟩
  have hLeft : (∑ i ∈ Icc 1 n, (2 * (dD (n - i))) * (2 * (dD i))) =
      4 * ∑ i ∈ Icc 1 n, (dD (n - i)) * dD i := by
    rw [mul_sum]
    exact sum_congr rfl fun _ _ ↦ by ring
  have hRight : (∑ i ∈ Icc 1 n, ((i * (n - i) : ℕ) : ℤ) * coeff (n - i) overpartitionSeries *
        coeff i signedTheta) =
      -(2 * ∑ i ∈ Icc 1 n with i ^ 2 ≤ n,
        (-1) ^ (i + 1) * (i : ℤ) ^ 2 * ((n : ℤ) - (i : ℤ) ^ 2) * pbar (n - i ^ 2)) := by
    rw [sum_mul_signedTheta, ← mul_neg, ← sum_neg_distrib]
    congr 1
    refine sum_congr rfl fun i hi ↦ ?_
    rw [Nat.cast_mul, Nat.cast_sub (mem_filter.mp hi).2, Nat.cast_pow,
      ← overpartition_card_eq_coeff_genFun, pow_succ]
    ring
  have hSecond := h.2
  rw [hLeft, hRight, neg_neg] at hSecond
  apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by decide)
  rw [← mul_assoc]
  exact hSecond

end MetaMathlibExt
