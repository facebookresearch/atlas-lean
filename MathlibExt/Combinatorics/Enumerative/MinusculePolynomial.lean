/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Minuscule polynomials of type A

We define the type-A minuscule polynomials and prove Ding and Zeng's formula for their
exponential generating function.
-/

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- **Type-A minuscule polynomial.** For a natural number $n$, the type-A minuscule polynomial
$N_n(x)$ is the polynomial with rational coefficients
$$N_n(x) = \frac{1}{4n + 2} \sum_{k=1}^{n-1} k (n - k) \binom{2n + 2}{2k + 1} x^k.$$
For $n = 0$ the sum is empty, so $N_0 = 0$.

Source: Ming-Jian Ding and Jiang Zeng, *Some New Results on the Minuscule Polynomials of
Type A*, Journal of Integer Sequences 28 (2025), Article 25.1.2, definition (1.1)
(arXiv:2308.16782v3, equation (1.1)). -/
public noncomputable def minusculePolynomialA (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.Icc 1 (n - 1),
    C ((k : ℚ) * ((n : ℚ) - k) * ((2 * n + 2).choose (2 * k + 1) : ℚ) / (4 * n + 2)) * X ^ k

/-- **The minuscule polynomial $N_1$ vanishes.** The type-A minuscule polynomial $N_1(x)$ is the
zero polynomial.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, table of `N_n(x)` after (1.1). -/
public theorem minusculePolynomialA_one : minusculePolynomialA 1 = 0 := by
  simp [minusculePolynomialA]

/-- **The minuscule polynomial $N_2$.** The type-A minuscule polynomial $N_2(x)$ equals $2x$.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, table of `N_n(x)` after (1.1). -/
public theorem minusculePolynomialA_two : minusculePolynomialA 2 = C 2 * X := by
  simp [minusculePolynomialA, Nat.choose]
  norm_num

/-- **The minuscule polynomial $N_3$.** The type-A minuscule polynomial $N_3(x)$ equals
$8x + 8x^2$.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, table of `N_n(x)` after (1.1). -/
public theorem minusculePolynomialA_three :
    minusculePolynomialA 3 = C 8 * X + C 8 * X ^ 2 := by
  rw [minusculePolynomialA, show Finset.Icc 1 (3 - 1) = {1, 2} by decide]
  simp [Nat.choose]
  norm_num

namespace minusculePolynomialA_egf

open Finset

/-- Split a binomial expansion into its even and odd powers. -/
private theorem binomial_parts (x : ℝ) (n : ℕ) :
    (1 + x) ^ (2 * n) =
      (∑ k ∈ range (n + 1), (x ^ 2) ^ k * (2 * n).choose (2 * k)) +
      x * ∑ k ∈ range n, (x ^ 2) ^ k * (2 * n).choose (2 * k + 1) := by
  have split (f : ℕ → ℝ) (m : ℕ) :
      ∑ j ∈ range (2 * m + 1), f j =
        (∑ k ∈ range (m + 1), f (2 * k)) + ∑ k ∈ range m, f (2 * k + 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ, sum_range_succ _ (2 * m + 2), sum_range_succ _ (2 * m + 1), ih,
        sum_range_succ _ (m + 1), sum_range_succ (fun k => f (2 * k + 1)) m, Nat.mul_succ]
      ring
  rw [add_comm 1 x, add_pow, split, mul_sum]
  simp only [one_pow, mul_one, pow_succ x (2 * _), pow_mul, mul_assoc, mul_left_comm]

/-- The two binomial rows in the expansion give the defining coefficient of the polynomial. -/
private theorem binomial_coeff (n k : ℕ) (hk : k ≤ n) :
    16 * ((k : ℝ) * (n - k) * (2 * n + 2).choose (2 * k + 1) / (4 * n + 2)) =
      4 * (n + 1) * (2 * n).choose (2 * k) - 2 * (2 * n + 2).choose (2 * k + 1) := by
  have h : (2 * n + 2).choose (2 * k + 1) * (2 * k + 1) * (2 * n + 1 - 2 * k) =
      (2 * n + 2) * ((2 * n).choose (2 * k) * (2 * n + 1)) := by
    rw [← Nat.add_one_mul_choose_eq (2 * n + 1) (2 * k), Nat.mul_assoc,
      ← Nat.choose_mul_succ_eq]
  have hreal := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast [Nat.cast_sub (by omega : 2 * k ≤ 2 * n + 1)] at hreal
  field_simp
  linear_combination 4 * hreal

private theorem evaluated (x : ℝ) (n : ℕ) :
    16 * x * aeval (x ^ 2) (minusculePolynomialA n) =
      2 * (n + 1) * x * ((1 + x) ^ (2 * n) + (1 - x) ^ (2 * n)) -
        ((1 + x) ^ (2 * (n + 1)) - (1 - x) ^ (2 * (n + 1))) := by
  have eval_sum : aeval (x ^ 2) (minusculePolynomialA n) =
      ∑ k ∈ range (n + 1),
        ((k : ℝ) * (n - k) * (2 * n + 2).choose (2 * k + 1) / (4 * n + 2)) * (x ^ 2) ^ k := by
    simp only [minusculePolynomialA, map_sum, map_mul, map_pow, aeval_C, aeval_X, map_div₀,
      map_sub, map_add, map_natCast, map_ofNat]
    apply sum_subset
    · intro k hk
      simp only [mem_Icc, mem_range] at *
      omega
    · intro k hk hout
      simp only [mem_Icc, mem_range] at *
      rcases (by omega : k = 0 ∨ k = n) with rfl | rfl <;> simp
  have even_part : (1 + x) ^ (2 * n) + (1 - x) ^ (2 * n) =
      2 * ∑ k ∈ range (n + 1), (x ^ 2) ^ k * (2 * n).choose (2 * k) := by
    rw [sub_eq_add_neg, binomial_parts x, binomial_parts (-x), neg_sq]
    ring
  have odd_part : (1 + x) ^ (2 * (n + 1)) - (1 - x) ^ (2 * (n + 1)) =
      2 * x * ∑ k ∈ range (n + 1), (x ^ 2) ^ k * (2 * n + 2).choose (2 * k + 1) := by
    rw [sub_eq_add_neg 1 x, binomial_parts x, binomial_parts (-x), neg_sq, Nat.mul_succ]
    ring
  rw [eval_sum, even_part, odd_part, ← mul_assoc]
  simp only [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun k hk => ?_
  linear_combination x * (x ^ 2) ^ k * binomial_coeff n k (by simpa using hk)

private theorem hasSum_affine_exp (a b t : ℝ) :
    HasSum (fun n : ℕ => (a * n + b) * (t ^ n / n.factorial))
      ((a * t + b) * Real.exp t) := by
  have hexp : HasSum (fun n : ℕ => t ^ n / n.factorial) (Real.exp t) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp t
  have hweighted : HasSum (fun n : ℕ => n * (t ^ n / n.factorial)) (t * Real.exp t) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
    refine (hexp.mul_left t).congr_fun fun n => ?_
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one, pow_succ]
    field_simp
  convert (hweighted.mul_left a).add (hexp.mul_left b) using 1
  · funext n
    ring
  · ring

end minusculePolynomialA_egf

/-- **Exponential generating function of the minuscule polynomials.** For all real numbers $x$
and $z$ with $x \ne 0$, the series $\sum_{n \ge 0} N_n(x^2)\, z^n / n!$ built from the type-A
minuscule polynomials $N_n$ has sum
$\frac{2x(1+x)^2 z - 1 - x^2}{16x} e^{(1+x)^2 z} +
\frac{2x(1-x)^2 z + 1 + x^2}{16x} e^{(1-x)^2 z}$.

The sum starts at $n = 0$, where $N_0 = 0$.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Proposition 10. -/
public theorem minusculePolynomialA_egf (x z : ℝ) (hx : x ≠ 0) :
    HasSum (fun n : ℕ => aeval (x ^ 2) (minusculePolynomialA n) * z ^ n / n.factorial)
      ((2 * x * (1 + x) ^ 2 * z - 1 - x ^ 2) / (16 * x) * Real.exp ((1 + x) ^ 2 * z) +
        (2 * x * (1 - x) ^ 2 * z + 1 + x ^ 2) / (16 * x) * Real.exp ((1 - x) ^ 2 * z)) := by
  have hplus := minusculePolynomialA_egf.hasSum_affine_exp (2 * x) (-1 - x ^ 2)
    ((1 + x) ^ 2 * z)
  have hminus := minusculePolynomialA_egf.hasSum_affine_exp (2 * x) (1 + x ^ 2)
    ((1 - x) ^ 2 * z)
  convert ((hplus.add hminus).div_const (16 * x)).congr_fun (g := fun n : ℕ =>
    aeval (x ^ 2) (minusculePolynomialA n) * z ^ n / n.factorial) ?_ using 1
  · ring
  · intro n
    have h := minusculePolynomialA_egf.evaluated x n
    simp only [pow_mul, pow_succ ((1 + x) ^ 2), pow_succ ((1 - x) ^ 2)] at h
    simp only [mul_pow]
    field_simp [hx]
    linear_combination z ^ n * h

end

end MetaMathlibExt
