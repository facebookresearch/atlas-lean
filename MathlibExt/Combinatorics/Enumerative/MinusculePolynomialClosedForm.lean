/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MinusculePolynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Binomial closed form of the minuscule polynomials

We prove Ding and Zeng's binomial closed form for the type-A minuscule polynomials $N_n$: the
identity $16x\, N_n(x^2) = 2(n+1)x \bigl((1+x)^{2n} + (1-x)^{2n}\bigr) -
\bigl((1+x)^{2n+2} - (1-x)^{2n+2}\bigr)$ of polynomials with rational coefficients. The proof
splits both binomial expansions into their even and odd powers and compares the coefficients of
$x^{2k+1}$.
-/

namespace MetaMathlibExt

open Polynomial

namespace minusculePolynomialA_comp_sq

open Finset

/-- Split a binomial expansion into its even and odd powers. -/
private theorem binomial_parts {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    (1 + x) ^ (2 * n) =
      (∑ k ∈ range (n + 1), (x ^ 2) ^ k * ((2 * n).choose (2 * k) : R)) +
      x * ∑ k ∈ range n, (x ^ 2) ^ k * ((2 * n).choose (2 * k + 1) : R) := by
  have split (f : ℕ → R) (m : ℕ) :
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

/-- The two binomial rows of the expansion give the defining coefficient of the polynomial. -/
private theorem binomial_coeff (n k : ℕ) (hk : k ≤ n) :
    16 * ((k : ℚ) * (n - k) * (2 * n + 2).choose (2 * k + 1) / (4 * n + 2)) =
      4 * (n + 1) * (2 * n).choose (2 * k) - 2 * (2 * n + 2).choose (2 * k + 1) := by
  have h : (2 * n + 2).choose (2 * k + 1) * (2 * k + 1) * (2 * n + 1 - 2 * k) =
      (2 * n + 2) * ((2 * n).choose (2 * k) * (2 * n + 1)) := by
    rw [← Nat.add_one_mul_choose_eq (2 * n + 1) (2 * k), Nat.mul_assoc,
      ← Nat.choose_mul_succ_eq]
  have hrat := congrArg (Nat.cast : ℕ → ℚ) h
  push_cast [Nat.cast_sub (by omega : 2 * k ≤ 2 * n + 1)] at hrat
  field_simp
  linear_combination 4 * hrat

end minusculePolynomialA_comp_sq

open minusculePolynomialA_comp_sq in
/-- **Binomial closed form of the minuscule polynomials.** For every natural number $n$, the
type-A minuscule polynomial $N_n$ satisfies the identity of polynomials with rational
coefficients
$16x\, N_n(x^2) = 2(n+1)x \bigl((1+x)^{2n} + (1-x)^{2n}\bigr) -
\bigl((1+x)^{2n+2} - (1-x)^{2n+2}\bigr)$.

Dividing by $16x$ gives $N_n(x^2) = \frac{n+1}{8} \bigl((1+x)^{2n} + (1-x)^{2n}\bigr) -
\frac{1}{16x} \bigl((1+x)^{2n+2} - (1-x)^{2n+2}\bigr)$; both sides vanish at $n = 0$.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Proposition 9. -/
public theorem minusculePolynomialA_comp_sq (n : ℕ) :
    C 16 * X * (minusculePolynomialA n).comp (X ^ 2) =
      C (2 * ((n : ℚ) + 1)) * X * ((1 + X) ^ (2 * n) + (1 - X) ^ (2 * n)) -
        ((1 + X) ^ (2 * n + 2) - (1 - X) ^ (2 * n + 2)) := by
  have comp_sum : (minusculePolynomialA n).comp (X ^ 2) =
      ∑ k ∈ Finset.range (n + 1),
        C ((k : ℚ) * (n - k) * (2 * n + 2).choose (2 * k + 1) / (4 * n + 2)) * (X ^ 2) ^ k := by
    rw [minusculePolynomialA, Polynomial.sum_comp]
    simp only [mul_comp, C_comp, X_pow_comp]
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Icc, Finset.mem_range] at *
      omega
    · intro k hk hout
      simp only [Finset.mem_Icc, Finset.mem_range] at *
      rcases (by omega : k = 0 ∨ k = n) with rfl | rfl <;> simp
  have even_part : ((1 : ℚ[X]) + X) ^ (2 * n) + (1 - X) ^ (2 * n) =
      2 * ∑ k ∈ Finset.range (n + 1), (X ^ 2) ^ k * ((2 * n).choose (2 * k) : ℚ[X]) := by
    rw [sub_eq_add_neg, binomial_parts X, binomial_parts (-X), neg_sq]
    ring
  have odd_part : ((1 : ℚ[X]) + X) ^ (2 * n + 2) - (1 - X) ^ (2 * n + 2) =
      2 * X * ∑ k ∈ Finset.range (n + 1),
        (X ^ 2) ^ k * ((2 * n + 2).choose (2 * k + 1) : ℚ[X]) := by
    rw [sub_eq_add_neg 1 X, show 2 * n + 2 = 2 * (n + 1) by ring, binomial_parts X,
      binomial_parts (-X), neg_sq]
    ring
  rw [comp_sum, even_part, odd_part]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h := congrArg C (binomial_coeff n k (by simpa [Nat.lt_succ_iff] using hk))
  simp only [map_mul, map_sub, map_add, map_one, map_ofNat, map_natCast] at h ⊢
  linear_combination X * (X ^ 2) ^ k * h

end MetaMathlibExt
