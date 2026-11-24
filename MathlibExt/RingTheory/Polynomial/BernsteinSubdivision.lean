/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Polynomial.BernsteinConversion
import Mathlib.Tactic.Linarith

/-!
# De Casteljau subdivision

Successive affine combinations evaluate Bernstein expansions and give the
coefficients of their restrictions to the two subintervals of a cut.
Reference: A. P. Smith, *Enclosure Methods for Systems of Polynomial Equations
and Inequalities* (2012), §3.3.2, equation (3.27), https://d-nb.info/1028327854/34.
-/

@[expose] public section

namespace bernsteinPolynomial

/-- The de Casteljau recurrence for real control coefficients. At depth `n`
only `c 0, ..., c n` are used. It is defined for every real interpolation
parameter; convex enclosure statements require that parameter in `[0,1]`. -/
noncomputable def deCasteljau (t : ℝ) (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => c 0
  | n + 1 => (1 - t) * deCasteljau t c n +
      t * deCasteljau t (fun j => c (j + 1)) n

/-- A depth-`n` de Casteljau evaluation depends only on indices at most `n`. -/
theorem deCasteljau_congr (t : ℝ) (n : ℕ) {c d : ℕ → ℝ}
    (h : ∀ j ≤ n, c j = d j) : deCasteljau t c n = deCasteljau t d n := by
  induction n generalizing c d with
  | zero => exact h 0 le_rfl
  | succ n ih =>
    simp only [deCasteljau]
    rw [ih (fun j hj => h j (by omega)), ih (fun j hj => h (j + 1) (by omega))]

/-- De Casteljau evaluation preserves addition of real coefficient sequences. -/
theorem deCasteljau_add (t : ℝ) (c d : ℕ → ℝ) (n : ℕ) :
    deCasteljau t (fun j => c j + d j) n = deCasteljau t c n + deCasteljau t d n := by
  induction n generalizing c d with
  | zero => rfl
  | succ n ih => simp only [deCasteljau, ih]; ring

/-- De Casteljau evaluation commutes with multiplication by a real scalar. -/
theorem deCasteljau_mul (t a : ℝ) (c : ℕ → ℝ) (n : ℕ) :
    deCasteljau t (fun j => a * c j) n = a * deCasteljau t c n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [deCasteljau, ih]; ring

/-- The diagonal of the de Casteljau triangle gives left-subinterval control
coefficients: evaluating them at `x` equals evaluating the original sequence
at `t*x`. This algebraic identity holds for all real `t,x` and every depth. -/
theorem deCasteljau_left (t x : ℝ) (c : ℕ → ℝ) (n : ℕ) :
    deCasteljau x (fun j => deCasteljau t c j) n = deCasteljau (x * t) c n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [deCasteljau, deCasteljau_add, deCasteljau_mul, ih]
    ring

/-- An interval containing the first `n+1` real control coefficients contains
all their depth-`n` de Casteljau values at parameters in `[0,1]`. -/
theorem deCasteljau_mem_Icc {t L U : ℝ} (ht : t ∈ Set.Icc 0 1)
    {c : ℕ → ℝ} {n : ℕ} (hc : ∀ j ≤ n, c j ∈ Set.Icc L U) :
    deCasteljau t c n ∈ Set.Icc L U := by
  induction n generalizing c with
  | zero => exact hc 0 le_rfl
  | succ n ih =>
    have h0 := ih (fun j hj => hc j (by omega))
    have h1 := ih (fun j hj => hc (j + 1) (by omega))
    simp only [deCasteljau, Set.mem_Icc] at *
    constructor
    · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr h1.1),
        mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr h0.1)]
    · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr h1.2),
        mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr h0.2)]

/-- The opposite edge of the de Casteljau triangle gives right-subinterval
control coefficients. Evaluation at `x` equals evaluation of the original
sequence at `t + (1-t)*x`, for all real `t,x` and every depth `n`. -/
theorem deCasteljau_right (t x : ℝ) (c : ℕ → ℝ) (n : ℕ) :
    deCasteljau x (fun j => deCasteljau t (fun i => c (i + j)) (n - j)) n =
      deCasteljau (t + (1 - t) * x) c n := by
  induction n generalizing c with
  | zero => simp [deCasteljau]
  | succ n ih =>
    rw [deCasteljau]
    have hhead : deCasteljau x
        (fun j => deCasteljau t (fun i => c (i + j)) (n + 1 - j)) n =
        (1 - t) * deCasteljau x
          (fun j => deCasteljau t (fun i => c (i + j)) (n - j)) n +
        t * deCasteljau x
          (fun j => deCasteljau t (fun i => c (i + j + 1)) (n - j)) n := by
      rw [← deCasteljau_mul, ← deCasteljau_mul, ← deCasteljau_add]
      apply deCasteljau_congr
      intro j hj
      rw [show n + 1 - j = (n - j) + 1 by omega, deCasteljau]
      congr 2
      apply deCasteljau_congr
      intro i _
      congr 1
      omega
    have htail : deCasteljau x
        (fun j => deCasteljau t (fun i => c (i + (j + 1))) (n + 1 - (j + 1))) n =
        deCasteljau x
          (fun j => deCasteljau t (fun i => c (i + j + 1)) (n - j)) n := by
      simp [Nat.add_assoc]
    rw [hhead, htail, ih c, ih (fun i => c (i + 1)), deCasteljau]
    ring

private theorem eval_succ_succ (n j : ℕ) (hj : j ≤ n) (t : ℝ) :
    (bernsteinPolynomial ℝ (n + 1) (j + 1)).eval t =
      (1 - t) * (bernsteinPolynomial ℝ n (j + 1)).eval t +
      t * (bernsteinPolynomial ℝ n j).eval t := by
  by_cases htop : j = n
  · subst j
    simp [bernsteinPolynomial, pow_succ]
    ring
  · have hlt : j < n := by omega
    have hn : n - j = n - (j + 1) + 1 := by omega
    simp only [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_natCast, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
      Nat.add_sub_add_right, Nat.choose_succ_succ', Nat.cast_add, Polynomial.eval_add]
    rw [hn]
    simp only [pow_succ]
    ring

open Finset

private theorem sum_eval_succ (t : ℝ) (c : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ range (n + 2), c j * (bernsteinPolynomial ℝ (n + 1) j).eval t) =
      (1 - t) * (∑ j ∈ range (n + 1), c j * (bernsteinPolynomial ℝ n j).eval t) +
      t * (∑ j ∈ range (n + 1), c (j + 1) * (bernsteinPolynomial ℝ n j).eval t) := by
  have hshift : (∑ j ∈ range (n + 1), c (j + 1) *
      (bernsteinPolynomial ℝ n (j + 1)).eval t) =
      (∑ j ∈ range (n + 1), c j * (bernsteinPolynomial ℝ n j).eval t) -
        c 0 * (1 - t) ^ n := by
    have h := sum_range_succ' (fun j => c j * (bernsteinPolynomial ℝ n j).eval t) (n + 1)
    rw [sum_range_succ] at h
    have hzero : (bernsteinPolynomial ℝ n (n + 1)).eval t = 0 := by
      rw [eq_zero_of_lt ℝ (Nat.lt_succ_self n), Polynomial.eval_zero]
    have hfirst : (bernsteinPolynomial ℝ n 0).eval t = (1 - t) ^ n := by
      simp [bernsteinPolynomial]
    rw [hzero, mul_zero, add_zero, hfirst] at h
    linarith
  rw [show n + 2 = (n + 1) + 1 by omega, sum_range_succ']
  have hterm : ∀ j ∈ range (n + 1), c (j + 1) *
      (bernsteinPolynomial ℝ (n + 1) (j + 1)).eval t =
      (1 - t) * (c (j + 1) * (bernsteinPolynomial ℝ n (j + 1)).eval t) +
      t * (c (j + 1) * (bernsteinPolynomial ℝ n j).eval t) := by
    intro j hj
    rw [eval_succ_succ n j (by simpa using mem_range.mp hj) t]
    ring
  rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, ← mul_sum, hshift]
  have hfirst : (bernsteinPolynomial ℝ (n + 1) 0).eval t = (1 - t) ^ (n + 1) := by
    simp [bernsteinPolynomial]
  rw [hfirst, pow_succ]
  ring

/-- De Casteljau evaluation equals the degree-`n` Bernstein expansion with
real coefficients `c 0, ..., c n`, at every real argument `t`. -/
theorem deCasteljau_eq_sum (t : ℝ) (c : ℕ → ℝ) (n : ℕ) :
    deCasteljau t c n =
      ∑ j ∈ range (n + 1), c j * (bernsteinPolynomial ℝ n j).eval t := by
  induction n generalizing c with
  | zero => simp [deCasteljau, bernsteinPolynomial]
  | succ n ih =>
    rw [deCasteljau, ih, ih]
    exact (sum_eval_succ t c n).symm

end bernsteinPolynomial
