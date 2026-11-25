/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Sum

/-!
# The factor `(x - 1)^n` of an alternating binomial sum

We use the cancellation in Agoh's second proof (INTEGERS 26 (2026), Article A9, §2).
A single polynomial in an auxiliary variable represents the products with one factor
omitted. Expanding it in monomials reduces the alternating sum to powers of `1 - X ^ j`.
-/

open Finset Polynomial

namespace MetaMathlibExt

-- If `P(Y) = ∏ j, (Y + t j)`, then evaluating `P.divX` at `-t i`
-- gives the constant term of the product omitting `i`, even when `t i = 0`.
private theorem eval_divX_prod_add_C {R : Type*} [CommRing R] (s : Finset ℕ) (t : ℕ → R)
    {i : ℕ} (hi : i ∈ s) :
    (∏ j ∈ s, (X + C (t j))).divX.eval (-t i) = ∏ j ∈ s.erase i, t j := by
  rw [← mul_prod_erase s (fun j ↦ X + C (t j)) hi]
  let q : R[X] := ∏ j ∈ s.erase i, (X + C (t j))
  change ((X + C (t i)) * q).divX.eval (-t i) = _
  have hX : (X * q).divX = q := by
    ext j
    simp
  rw [add_mul, divX_add, hX, divX_C_mul, eval_add, eval_mul, eval_C]
  have hq := congrArg (eval (-t i)) (X_mul_divX_add q)
  simp only [eval_add, eval_mul, eval_X, eval_C] at hq
  rw [← hq, neg_mul, neg_add_eq_sub, sub_add_cancel, coeff_zero_eq_eval_zero]
  simp [q, eval_prod]

-- Each monomial gives precisely the binomial expansion of `(1 - X ^ j) ^ n`.
private theorem alternating_sum_X_pow (n j : ℕ) :
    ∑ i ∈ range (n + 1), (-1 : ℝ[X]) ^ i * (n.choose i : ℝ[X]) * (X ^ i) ^ j =
      (1 - X ^ j) ^ n := by
  rw [sub_eq_neg_add, add_pow]
  apply sum_congr rfl
  intro i _
  simp only [one_pow, mul_one, neg_pow (X ^ j : ℝ[X]), ← pow_mul, Nat.mul_comm j i]
  exact mul_right_comm _ _ _

private theorem X_sub_one_pow_dvd_alternating_sum_eval (n : ℕ) (p : (ℝ[X])[X]) :
    (X - 1 : ℝ[X]) ^ n ∣
      ∑ i ∈ range (n + 1), (-1 : ℝ[X]) ^ i * (n.choose i : ℝ[X]) * p.eval (X ^ i) := by
  have heval (z : ℝ[X]) : p.eval z =
      ∑ j ∈ range (p.natDegree + 1), p.coeff j * z ^ j := by
    rw [eval_eq_sum, sum_over_range _ (fun _ ↦ zero_mul _)]
  simp_rw [heval, mul_sum]
  rw [sum_comm]
  apply dvd_sum
  intro j _
  calc
    (X - 1 : ℝ[X]) ^ n ∣ p.coeff j * (1 - X ^ j) ^ n := by
      have hdvd : (X - 1 : ℝ[X]) ∣ 1 - X ^ j := by
        simpa only [neg_sub, one_pow] using
          dvd_neg.mpr (sub_dvd_pow_sub_pow (X : ℝ[X]) 1 j)
      exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hdvd n) (p.coeff j)
    _ = p.coeff j * ∑ i ∈ range (n + 1),
        (-1 : ℝ[X]) ^ i * (n.choose i : ℝ[X]) * (X ^ i) ^ j := by
      rw [alternating_sum_X_pow]
    _ = _ := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ mul_left_comm (p.coeff j) _ _

/-- **The factor $(x - 1)^n$ of an alternating binomial sum.** For every real number $a$ and
every natural number $n$, the polynomial $(x - 1)^n$ divides, in $\mathbb{R}[x]$, the polynomial
$$H_n(x; a) = \sum_{i=0}^{n} (-1)^i \binom{n}{i} \prod_{0 \le k \le n,\ k \ne i} (x^k + a).$$

For $a \ne -1$ (the paper's condition), $H_n(x; a)$ is the numerator of
$G_n(x; a) = \sum_{i=0}^{n} (-1)^i \binom{n}{i} / (x^i + a)$ over the common denominator
$\prod_{k=0}^{n} (x^k + a)$; at $a = -1$ the factor $x^0 + a$ is zero and only the polynomial
statement remains.

Source: Takashi Agoh, *An Intrinsic Factor of an Alternating Sum Involving Certain Rational
Functions*, INTEGERS 26 (2026), Article A9, Theorem 1.1 (`integers-2026-A9-thm-1-1`). -/
public theorem X_sub_one_pow_dvd_alternating_sum_prod_X_pow_add_C (n : ℕ) (a : ℝ) :
    (X - 1 : ℝ[X]) ^ n ∣ ∑ i ∈ Finset.range (n + 1),
      (-1 : ℝ[X]) ^ i * (n.choose i : ℝ[X]) *
        ∏ k ∈ (Finset.range (n + 1)).erase i, (X ^ k + C a) := by
  let t (i : ℕ) : ℝ[X] := X ^ i + C a
  let p : (ℝ[X])[X] := (∏ j ∈ range (n + 1), (X + C (t j))).divX
  have hsum := X_sub_one_pow_dvd_alternating_sum_eval n (p.comp (-(X + C (C a))))
  simp only [eval_comp, eval_neg, eval_add, eval_X, eval_C] at hsum
  convert hsum using 1
  exact sum_congr rfl fun i hi ↦
    congrArg ((-1 : ℝ[X]) ^ i * (n.choose i : ℝ[X]) * ·)
      (eval_divX_prod_add_C _ t hi).symm

/-- **The factor $(x - 1)^n$ for polynomials with distinct real roots.** Let $c$ be a real
number, let $s$ be a finite set of real numbers, and let $f(x) = c \prod_{r \in s} (x - r)$ in
$\mathbb{R}[x]$. For every natural number $n$, the polynomial $(x - 1)^n$ divides the polynomial
$$\sum_{i=0}^{n} (-1)^i \binom{n}{i} \prod_{0 \le k \le n,\ k \ne i} f(x^k).$$

For $c \ne 0$ and $1 \notin s$ (the paper's conditions), this polynomial is the numerator of
$Q_n(x; f) = \sum_{i=0}^{n} (-1)^i \binom{n}{i} / f(x^i)$ over the common denominator
$\prod_{k=0}^{n} f(x^k)$; for $c = 0$ or $1 \in s$ some $f(x^k)$ is zero and only the
polynomial statement remains.

Source: Takashi Agoh, *An Intrinsic Factor of an Alternating Sum Involving Certain Rational
Functions*, INTEGERS 26 (2026), Article A9, Theorem 3.1 (`integers-2026-A9-thm-3-1`). -/
public theorem X_sub_one_pow_dvd_alternating_sum_prod_comp_X_pow (n : ℕ) (c : ℝ)
    (s : Finset ℝ) :
    (X - 1 : ℝ[X]) ^ n ∣ ∑ i ∈ Finset.range (n + 1),
      (-1 : ℝ[X]) ^ i * (n.choose i : ℝ[X]) *
        ∏ k ∈ (Finset.range (n + 1)).erase i, (C c * ∏ r ∈ s, (X - C r)).comp (X ^ k) := by
  let f : ℝ[X] := C c * ∏ r ∈ s, (X - C r)
  let t (i : ℕ) : ℝ[X] := f.comp (X ^ i)
  let p : (ℝ[X])[X] := (∏ j ∈ range (n + 1), (X + C (t j))).divX
  let F : (ℝ[X])[X] := f.map C
  have hF (i : ℕ) : F.eval (X ^ i) = t i := by
    change (f.map C).eval (X ^ i) = f.eval₂ C (X ^ i)
    rw [eval_map]
  have hprod (i : ℕ) (hi : i ∈ range (n + 1)) :
      (p.comp (-F)).eval (X ^ i) = ∏ k ∈ (range (n + 1)).erase i, t k := by
    rw [eval_comp, eval_neg, hF]
    exact eval_divX_prod_add_C _ t hi
  convert X_sub_one_pow_dvd_alternating_sum_eval n (p.comp (-F)) using 1
  exact sum_congr rfl fun i hi ↦
    congrArg ((-1 : ℝ[X]) ^ i * (n.choose i : ℝ[X]) * ·) (hprod i hi).symm

end MetaMathlibExt
