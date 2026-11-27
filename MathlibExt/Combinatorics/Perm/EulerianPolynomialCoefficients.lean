/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Combinatorics.Perm.EulerianCuts
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.NormNum

/-!
# Binomial polynomials for descent counts

For `n,d : ℕ`, define `P_(n,d)(X) = (1/n!) ∏_(j=0)^(n-1) (X+j-d)` in `ℚ[X]`. It has degree at
most `n` and leading coefficient `1/n!`.

When `0<n` and `d<n`, evaluating at the positive integer `m+1` gives `choose(n+m-d,n)`. Its
constant coefficient is zero; evaluation at `1` is one only for `d=0`, and evaluation at `2`
gives `n+1`, `1`, or `0` for `d=0`, `d=1`, or larger descent counts.

References: Stanley, *Enumerative Combinatorics*, Volume 1, Chapter 3; Loday, *Cyclic
Homology*, Section 4.5.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Equiv.Perm

/-- For `n,d : ℕ`, write `P_(n,d)(X) = (1/n!) ∏ j=0,...,n-1, (X+j-d)` in `ℚ[X]`, with the empty
product equal to `1`. `descentBinomialPolynomial n d` is this rational polynomial,
equivalently the rising Pochhammer polynomial at `X-d` multiplied by `1/n!`. -/
def descentBinomialPolynomial (n d : ℕ) : Polynomial ℚ :=
  Polynomial.C ((Nat.factorial n : ℚ)⁻¹) *
    (_root_.ascPochhammer ℚ n).comp (Polynomial.X - Polynomial.C (d : ℚ))

/-- For `n,d : ℕ`, the rational polynomial satisfies `descentBinomialPolynomial n d = C((n!:ℚ)⁻¹)
* ∏ j ∈ Finset.range n, (X + C((j:ℚ)-(d:ℚ)))`. The subtraction in each factor is in `ℚ`; the
product is `1` for `n=0`. -/
theorem descentBinomialPolynomial_eq_prod (n d : ℕ) :
    descentBinomialPolynomial n d = Polynomial.C ((Nat.factorial n : ℚ)⁻¹) *
      ∏ j ∈ Finset.range n, (Polynomial.X + Polynomial.C ((j : ℚ) - d)) := by
  unfold descentBinomialPolynomial
  congr 1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [_root_.ascPochhammer_succ_right, Polynomial.mul_comp, ih, Finset.prod_range_succ]
    congr 1
    simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.natCast_comp]
    rw [← Polynomial.C_eq_natCast, Polynomial.C_sub]
    ring

/-- For `n,d : ℕ`, write `P_(n,d)(X) = (1/n!) ∏ j=0,...,n-1, (X+j-d)` in `ℚ[X]`, with the empty
product equal to `1`. The natural degree satisfies `(descentBinomialPolynomial n d).natDegree
≤ n`. -/
theorem descentBinomialPolynomial_natDegree_le (n d : ℕ) :
    (descentBinomialPolynomial n d).natDegree ≤ n := by
  unfold descentBinomialPolynomial
  refine Polynomial.natDegree_C_mul_le _ _ |>.trans ?_
  exact Polynomial.natDegree_comp_le.trans_eq (by
    rw [_root_.ascPochhammer_natDegree, Polynomial.natDegree_X_sub_C, mul_one])

/-- For `n,d : ℕ`, write `P_(n,d)(X) = (1/n!) ∏ j=0,...,n-1, (X+j-d)` in `ℚ[X]`, with the empty
product equal to `1`. The coefficient of `X^n` is `(descentBinomialPolynomial n d).coeff n =
(n!:ℚ)⁻¹`. -/
theorem descentBinomialPolynomial_coeff_degree (n d : ℕ) :
    (descentBinomialPolynomial n d).coeff n = (Nat.factorial n : ℚ)⁻¹ := by
  rw [descentBinomialPolynomial, Polynomial.coeff_C_mul]
  have h := Polynomial.coeff_comp_degree_mul_degree
    (p := _root_.ascPochhammer ℚ n) (q := Polynomial.X - Polynomial.C (d : ℚ))
    (by rw [Polynomial.natDegree_X_sub_C]; exact one_ne_zero)
  have hc : ((_root_.ascPochhammer ℚ n).comp (Polynomial.X - Polynomial.C (d : ℚ))).coeff n = 1 := by
    simpa only [_root_.ascPochhammer_natDegree, Polynomial.natDegree_X_sub_C,
      mul_one, (_root_.monic_ascPochhammer ℚ n).leadingCoeff,
      Polynomial.leadingCoeff_X_sub_C, one_pow, one_mul] using h
  rw [hc, mul_one]

/-- For `n,d : ℕ`, write `P_(n,d)(X) = (1/n!) ∏ j=0,...,n-1, (X+j-d)` in `ℚ[X]`, with the empty
product equal to `1`. For `x : ℚ`, `P_(n,d)(x) = ∑ i : Fin(n+1), coeff_i(P_(n,d)) * x^i.val`. -/
theorem descentBinomialPolynomial_eval_eq_sum (n d : ℕ) (x : ℚ) :
    (descentBinomialPolynomial n d).eval x =
      ∑ i : Fin (n + 1), (descentBinomialPolynomial n d).coeff i.val * x ^ i.val := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (descentBinomialPolynomial_natDegree_le n d))]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

/-- For `n,d : ℕ`, write `P_(n,d)(X) = (1/n!) ∏ j=0,...,n-1, (X+j-d)` in `ℚ[X]`, with the empty
product equal to `1`. If `0<n` and `d<n`, then for every `m : ℕ`, `P_(n,d)(m+1) = (Nat.choose
(n+m-d) n : ℚ)`. -/
theorem descentBinomialPolynomial_eval_succ (n d m : ℕ) (hn : 0 < n) (hd : d < n) :
    (descentBinomialPolynomial n d).eval (m + 1 : ℚ) = ((n + m - d).choose n : ℚ) := by
  classical
  simp only [descentBinomialPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  by_cases hdm : d ≤ m
  · let a := n + m - d
    have ha : n ≤ a := by dsimp [a]; omega
    have harg : a - (n - 1) = m + 1 - d := by dsimp [a]; omega
    have hcast : (m + 1 : ℚ) - d = ((m + 1 - d : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    have hchoose := Nat.cast_choose_eq_ascPochhammer_div (K := ℚ) a n
    rw [harg] at hchoose
    rw [hcast]
    calc
      (Nat.factorial n : ℚ)⁻¹ * (_root_.ascPochhammer ℚ n).eval ((m + 1 - d : ℕ) : ℚ) =
          (_root_.ascPochhammer ℚ n).eval ((m + 1 - d : ℕ) : ℚ) / Nat.factorial n := by
            simp only [div_eq_mul_inv]
            ring
      _ = (a.choose n : ℚ) := hchoose.symm
  · have harg : (m + 1 : ℚ) - d = -((d - (m + 1) : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      ring
    have hsmall : d - (m + 1) < n := by omega
    rw [harg, _root_.ascPochhammer_eval_neg_coe_nat_of_lt hsmall, mul_zero,
      Nat.choose_eq_zero_of_lt (by omega : n + m - d < n)]
    rfl

/-- For `n,d : ℕ`, write `P_(n,d)(X) = (1/n!) ∏ j=0,...,n-1, (X+j-d)` in `ℚ[X]`, with the empty
product equal to `1`. If `0<n` and `d<n`, the constant coefficient satisfies
`(descentBinomialPolynomial n d).coeff 0 = 0`. -/
theorem descentBinomialPolynomial_coeff_zero (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    (descentBinomialPolynomial n d).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp only [descentBinomialPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, zero_sub]
  rw [_root_.ascPochhammer_eval_neg_coe_nat_of_lt hd, mul_zero]

/-- For `n,d : ℕ`, write `P_(n,d)(X) = (1/n!) ∏ j=0,...,n-1, (X+j-d)` in `ℚ[X]`, with the empty
product equal to `1`. If `0<n` and `d<n`, `P_(n,d)(1) = if d=0 then 1 else 0`. -/
theorem descentBinomialPolynomial_eval_one (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    (descentBinomialPolynomial n d).eval 1 = if d = 0 then 1 else 0 := by
  have h := descentBinomialPolynomial_eval_succ n d 0 hn hd
  norm_num only [Nat.cast_zero, Nat.add_zero, zero_add] at h
  rw [h]
  split_ifs with hzero
  · subst d
    simp
  · rw [Nat.choose_eq_zero_of_lt (by omega : n - d < n)]
    rfl

/-- For `n,d : ℕ`, write `P_(n,d)(X) = (1/n!) ∏ j=0,...,n-1, (X+j-d)` in `ℚ[X]`, with the empty
product equal to `1`. If `0<n` and `d<n`, `P_(n,d)(2) = if d=0 then (n+1:ℚ) else if d=1 then 1
else 0`. -/
theorem descentBinomialPolynomial_eval_two (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    (descentBinomialPolynomial n d).eval 2 =
      if d = 0 then (n + 1 : ℚ) else if d = 1 then 1 else 0 := by
  have h : (descentBinomialPolynomial n d).eval 2 = ((n + 1 - d).choose n : ℚ) := by
    convert descentBinomialPolynomial_eval_succ n d 1 hn hd using 1 <;> norm_num
  rw [h]
  split_ifs with hzero hone
  · subst d
    simp
  · subst d
    simp
  · rw [Nat.choose_eq_zero_of_lt (by omega : n + 1 - d < n)]
    rfl

end Equiv.Perm
