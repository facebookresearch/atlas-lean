/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import MathlibExt.Combinatorics.Enumerative.SignedStirlingFirst
public import MathlibExt.NumberTheory.Bernoulli.BernoulliSecondKind
import Mathlib.Algebra.BigOperators.Intervals
import MathlibExt.NumberTheory.Bernoulli.BernoulliPolynomialFallingFactorial
import MathlibExt.NumberTheory.Bernoulli.BernoulliSecondKindStirlingSum
import MathlibExt.NumberTheory.Bernoulli.StirlingInversion
import MathlibExt.NumberTheory.BernoulliSecondKindBernoulliSecondEqNegSum

/-!
# Falling factorials in the Bernoulli polynomial basis

For every natural number `n`, the rational falling-factorial polynomial of order `n` expands
in the Bernoulli polynomials (with `B₁(X) = X - 1/2`) with a second-kind Bernoulli number
and a sum weighted by signed Stirling numbers of the first kind. For positive `n`, the
proof applies Stirling inversion coefficientwise to the centered Bernoulli polynomial
expansion, then identifies the constant correction using the second-kind Bernoulli sum.

## References

* Bakir Farhi, *Formulas Involving Bernoulli and Stirling Numbers of Both Kinds*,
  Journal of Integer Sequences 28 (2025), Article 25.2.6, pp. 1–16, Theorem 5.
  The proof uses Theorem 1, Lemma 3 and Theorem 4 as in the paper, via
  `bernoulli_poly_eq`, `stirling_inversion_iff` and `bernoulliSecond_eq_neg_sum`.
* Hans Rademacher, *Topics in Analytic Number Theory*, Springer-Verlag, 1973,
  Chapter 1, §2, Formula (2.2), cited by Farhi for the falling-factorial expression
  of the Bernoulli polynomials.
* Steven Roman, *The Umbral Calculus*, Academic Press, 1984, §3.2, pp. 113–114,
  for the normalization of the Bernoulli numbers of the second kind.
-/

namespace MathlibExt.NumberTheory.BernoulliSecondKindWanted

open Finset MetaMathlibExt
open Polynomial (C)

-- Normalize both families by their positive index and apply rational Stirling inversion
-- to each coefficient of the centered expansion.
private theorem descPochhammer_succ_eq_centered_sum (n : ℕ) :
    descPochhammer ℚ (n + 1) = ∑ k ∈ Icc 1 (n + 1),
      C ((n + 1 : ℚ) / k * (signedStirlingFirst n (k - 1) : ℚ)) *
        (Polynomial.bernoulli k - C (bernoulli k)) := by
  ext j
  let u (m : ℕ) : ℚ := (descPochhammer ℚ (m + 1)).coeff j / (m + 1)
  let v (m : ℕ) : ℚ :=
    (Polynomial.bernoulli (m + 1) - C (bernoulli (m + 1))).coeff j / (m + 1)
  have hv (m : ℕ) : v m = ∑ k ∈ range (m + 1), (Nat.stirlingSecond m k : ℚ) * u k := by
    have h : Polynomial.bernoulli (m + 1) - C (bernoulli (m + 1)) =
        ∑ k ∈ range (m + 1), C ((m + 1 : ℚ) / (k + 1) * (Nat.stirlingSecond m k : ℚ)) *
          descPochhammer ℚ (k + 1) := by
      rw [bernoulli_poly_eq, add_sub_cancel_left, ← Ico_add_one_right_eq_Icc,
        sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_right, Nat.one_add, Nat.succ_sub_one, Nat.cast_succ]
    have hc := congrArg (fun p : Polynomial ℚ => p.coeff j) h
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul] at hc
    simp only [u, v]
    rw [hc, sum_div]
    refine sum_congr rfl fun k _ => ?_
    field_simp
  have hu := (stirling_inversion_iff u v).mpr hv n
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right, Nat.one_add, Nat.succ_sub_one, Nat.cast_succ,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  calc
    _ = u n * (n + 1 : ℚ) := (div_mul_cancel₀ _ (by positivity : (n + 1 : ℚ) ≠ 0)).symm
    _ = _ := by
      rw [hu, sum_mul]
      refine sum_congr rfl fun k _ => ?_
      dsimp [v]
      ring

/-- **Falling factorials in the Bernoulli polynomial basis.** Let $B_m^*$ be the Bernoulli
numbers of the second kind, $B_k(X)$ the Bernoulli polynomials over $\mathbb{Q}$ (so that
$B_1(X) = X - 1/2$), $s(m, j)$ the signed Stirling numbers of the first kind and
$X^{\underline{n}} = X(X-1)\cdots(X-n+1)$ the falling factorial. For every natural number
$n$, in $\mathbb{Q}[X]$,
$$X^{\underline{n}} = B_n^* + \sum_{k=1}^{n} \frac{n}{k} \, s(n-1, k-1) \, B_k(X).$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Theorem 5. -/
public theorem descPochhammer_eq (n : ℕ) :
    descPochhammer ℚ n =
      Polynomial.C (MetaMathlibExt.bernoulliSecond n) +
        ∑ k ∈ Finset.Icc 1 n, Polynomial.C
          ((n : ℚ) / k * (MetaMathlibExt.signedStirlingFirst (n - 1) (k - 1) : ℚ)) *
          Polynomial.bernoulli k := by
  cases n with
  | zero => simp [bernoulliSecond_eq_sum]
  | succ n =>
    rw [descPochhammer_succ_eq_centered_sum, bernoulliSecond_eq_neg_sum _ (Nat.succ_pos n)]
    simp only [Nat.succ_sub_one, Nat.cast_succ, mul_sub, ← map_mul, sum_sub_distrib, ← map_sum,
      map_neg]
    rw [sub_eq_add_neg, add_comm]

end MathlibExt.NumberTheory.BernoulliSecondKindWanted
