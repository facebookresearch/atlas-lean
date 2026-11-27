/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.RingTheory.Polynomial.BernsteinConversion
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite

/-!
# Tensor-product Bernstein conversion

For a finite variable type and a coordinatewise degree bound `n`, the products
of univariate Bernstein polynomials give an exact expansion of a real
multivariate polynomial. The coefficients are explicit sums of power-basis
coefficients times products of binomial ratios. The identity holds at every
real argument, including outside the unit cube. Empty variable types and
zero coordinate degrees are allowed.

Reference: A. P. Smith, *Enclosure Methods for Systems of Polynomial Equations
and Inequalities* (2012), §3.1.3, Theorem 3.2, equation (3.9),
https://d-nb.info/1028327854/34.
-/

@[expose] public section

namespace MvPolynomial

open Finset

variable {ι : Type*} [Fintype ι]

/-- For a finite variable type, the tensor-product Bernstein polynomial with
coordinate degrees `n` and index `k`: the product of
`choose (n i) (k i) * X i ^ k i * (1 - X i) ^ (n i - k i)`.
Subtraction in the exponents is truncated natural subtraction. The expansion
uses indices satisfying `k i ≤ n i` in every coordinate. -/
noncomputable def bernstein (n k : ι → ℕ) : MvPolynomial ι ℝ :=
  ∏ i, C ((n i).choose (k i) : ℝ) * X i ^ k i * (1 - X i) ^ (n i - k i)

/-- For finitely many variables, the Bernstein coefficient of a real polynomial `p` at index `k`
and coordinate degrees `n`: sum over the power-basis support of `p`, multiplying
each coefficient by `∏ i, choose (k i) (d i) / choose (n i) (d i)`.
A ratio with zero denominator is zero, by the convention for real division.
Reconstruction requires `p.degreeOf i ≤ n i` for every coordinate. -/
noncomputable def bernsteinCoeff (n : ι → ℕ) (p : MvPolynomial ι ℝ) (k : ι → ℕ) : ℝ :=
  p.coeff.sum fun d c => c * ∏ i, ((k i).choose (d i) : ℝ) / (n i).choose (d i)

/-- Evaluating a tensor-product Bernstein polynomial is the product of its
univariate Bernstein evaluations, over finitely many variables and at every real argument. -/
theorem eval_bernstein (n k : ι → ℕ) (x : ι → ℝ) :
    eval x (bernstein n k) = ∏ i, (bernsteinPolynomial ℝ (n i) (k i)).eval (x i) := by
  simp [bernstein, bernsteinPolynomial]

@[simp] theorem bernsteinCoeff_zero (n k : ι → ℕ) :
    bernsteinCoeff n (0 : MvPolynomial ι ℝ) k = 0 := by
  simp [bernsteinCoeff]

/-- A monomial's Bernstein coefficient is its scalar coefficient times the
product over the finite variable type of the coordinate binomial ratios.
This formula needs no degree bound; any ratio with zero denominator is zero. -/
@[simp] theorem bernsteinCoeff_monomial (n k : ι → ℕ) (d : ι →₀ ℕ) (c : ℝ) :
    bernsteinCoeff n (monomial d c) k =
      c * ∏ i, ((k i).choose (d i) : ℝ) / (n i).choose (d i) := by
  exact sum_monomial_eq (by simp)

@[simp] theorem bernsteinCoeff_C (n k : ι → ℕ) (c : ℝ) :
    bernsteinCoeff n (C c) k = c := by
  change bernsteinCoeff n (monomial 0 c) k = c
  rw [bernsteinCoeff_monomial]
  simp

/-- At fixed coordinate degrees and index, Bernstein coefficients preserve
addition of real polynomials in finitely many variables, without a degree hypothesis. -/
@[simp] theorem bernsteinCoeff_add (n k : ι → ℕ) (p q : MvPolynomial ι ℝ) :
    bernsteinCoeff n (p + q) k = bernsteinCoeff n p k + bernsteinCoeff n q k := by
  unfold bernsteinCoeff
  rw [AddMonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul ..)

/-- At fixed coordinate degrees and index, Bernstein coefficients commute
with multiplication by a real scalar for polynomials in finitely many variables,
without a degree hypothesis. -/
@[simp] theorem bernsteinCoeff_smul (n k : ι → ℕ) (c : ℝ) (p : MvPolynomial ι ℝ) :
    bernsteinCoeff n (c • p) k = c * bernsteinCoeff n p k := by
  unfold bernsteinCoeff
  rw [AddMonoidAlgebra.coeff_smul]
  rw [Finsupp.sum_smul_index (by simp)]
  simp only [mul_assoc, Finsupp.mul_sum]

@[simp] theorem bernsteinCoeff_neg (n k : ι → ℕ) (p : MvPolynomial ι ℝ) :
    bernsteinCoeff n (-p) k = -bernsteinCoeff n p k := by
  simpa only [neg_one_smul, neg_one_mul] using bernsteinCoeff_smul n k (-1) p

variable [DecidableEq ι]

private theorem monomial_sum_bernstein (n : ι → ℕ) (d : ι →₀ ℕ)
    (hd : ∀ i, d i ≤ n i) (x : ι → ℝ) :
    ∑ k : (i : ι) → Fin (n i + 1),
      (∏ i, ((k i).val.choose (d i) : ℝ) / (n i).choose (d i)) *
        eval x (bernstein n (fun i => k i)) = ∏ i, x i ^ d i := by
  simp_rw [eval_bernstein, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (j : Fin (n i + 1)) =>
    ((j.val.choose (d i) : ℝ) / (n i).choose (d i)) *
      (bernsteinPolynomial ℝ (n i) j).eval (x i))]
  apply prod_congr rfl
  intro i _
  simpa only [Finset.sum_range] using
    bernsteinPolynomial.monomial_bernstein (n i) (d i) (hd i) (x i)

/-- For finitely many variables, if each coordinate degree of a real polynomial `p` is bounded
by `n`, then at every real argument `x`, `p` evaluates to the sum of its explicit
Bernstein coefficients times the corresponding tensor-product basis values.
The sum ranges over all `k` with `0 ≤ k i ≤ n i`. -/
theorem eval_eq_sum_bernstein {n : ι → ℕ} {p : MvPolynomial ι ℝ}
    (hp : ∀ i, p.degreeOf i ≤ n i) (x : ι → ℝ) :
    eval x p = ∑ k : (i : ι) → Fin (n i + 1),
      bernsteinCoeff n p (fun i => k i) * eval x (bernstein n (fun i => k i)) := by
  classical
  rw [eval_eq']
  simp only [bernsteinCoeff, sum_def, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  simp_rw [mul_assoc]
  rw [← mul_sum, monomial_sum_bernstein n d
    (fun i => (degreeOf_le_iff.mp (hp i)) d hd) x]

/-- Every real polynomial in finitely many variables whose degree in each coordinate `i` is
at most `n i` equals the sum of its explicit Bernstein coefficients times the
tensor-product Bernstein polynomials, indexed by `k i : Fin (n i + 1)`. -/
theorem eq_sum_bernstein {n : ι → ℕ} {p : MvPolynomial ι ℝ}
    (hp : ∀ i, p.degreeOf i ≤ n i) :
    p = ∑ k : (i : ι) → Fin (n i + 1),
      C (bernsteinCoeff n p (fun i => k i)) * bernstein n (fun i => k i) := by
  apply MvPolynomial.funext
  intro x
  simpa only [map_sum, map_mul, eval_C] using eval_eq_sum_bernstein hp x

end MvPolynomial
