/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

/-!
# Coefficients and polynomials in Tonien's Fibonacci series for `π²`
-/

namespace MetaMathlibExt

/-- **Fibonacci closed form of the sequence $a_n$.** Let $(a_n)_{n \ge 0}$ be real numbers with
$a_0 = -8\sqrt{5}/250$, $a_1 = (25 - 4\sqrt{5})/250$ and $a_{n+1} = a_n + a_{n-1}$ for $n \ge 1$,
and write $F_m$ for the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$). Then for every $n \ge 0$,

$$a_{n+1} = \frac{25 - 4\sqrt{5}}{250} F_{n+1} - \frac{8\sqrt{5}}{250} F_n.$$

The paper states $a_n = \frac{25 - 4\sqrt{5}}{250} F_n - \frac{8\sqrt{5}}{250} F_{n-1}$ for all
$n \ge 0$ with the convention $F_{-1} = 1$; its case $n = 0$ is the initial value $a_0$.

Source: Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024), no. 1,
Lemma 2.3 (`fq-2024-tonien10292023-lem-2.3`). -/
public theorem fibPiSquared_coeff_eq_fib (a : ℕ → ℝ) (ha0 : a 0 = -(8 * √5) / 250)
    (ha1 : a 1 = (25 - 4 * √5) / 250) (ha : ∀ n, 1 ≤ n → a (n + 1) = a n + a (n - 1)) (n : ℕ) :
    a (n + 1) = (25 - 4 * √5) / 250 * Nat.fib (n + 1) - 8 * √5 / 250 * Nat.fib n := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using ha1
  | one =>
    rw [ha 1 (by decide)]
    simp [ha0, ha1, sub_eq_add_neg, neg_div]
  | more n ih₀ ih₁ =>
    rw [ha (n + 2) (by omega), show n + 2 - 1 = n + 1 by rfl, ih₁, ih₀,
      Nat.fib_add_two (n := n + 1), Nat.fib_add_two (n := n)]
    push_cast
    ring

open Finset Polynomial

namespace fibPiSquared_poly_eq_sum

private noncomputable def linearFactor (k : ℕ) : ℤ[X] := 2 * X + (k : ℤ[X])

private noncomputable def squareFactor (t : ℕ) : ℤ[X] := (X + (t : ℤ[X])) ^ 2

/-- The signed product multiplying the binomial coefficient at index `j`. -/
private noncomputable def term (n j : ℕ) : ℤ[X] :=
  (-1) ^ j * (∏ k ∈ Ico (2 * j + 3) (2 * n + 1), linearFactor k) *
    ∏ t ∈ Ico 1 (j + 1), squareFactor t

private theorem term_succ {n j : ℕ} (hj : j < n) :
    term (n + 1) j = (2 * X + C (2 * n + 1 : ℤ)) * (2 * X + C (2 * n + 2 : ℤ)) * term n j := by
  unfold term
  rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega,
    prod_Ico_succ_top (by omega : 2 * j + 3 ≤ 2 * n + 1 + 1),
    prod_Ico_succ_top (by omega : 2 * j + 3 ≤ 2 * n + 1)]
  simp only [linearFactor, map_add, map_mul, map_ofNat, map_natCast, map_one]
  push_cast
  ring

private theorem term_shift (n j : ℕ) :
    term (n + 1) (j + 1) = -((X + 1) ^ 2 * (term n j).comp (X + 1)) := by
  have hlinear (k : ℕ) : (linearFactor k).comp (X + 1) = linearFactor (k + 2) := by
    simp [linearFactor, mul_comp]
    ring
  have hsquare (t : ℕ) : (squareFactor t).comp (X + 1) = squareFactor (t + 1) := by
    simp [squareFactor, pow_comp, add_assoc, add_comm]
  simp only [term, mul_comp, pow_comp, neg_comp, one_comp, Polynomial.prod_comp, hlinear, hsquare]
  rw [prod_Ico_add' linearFactor, prod_Ico_add' squareFactor,
    show 2 * (j + 1) + 3 = 2 * j + 3 + 2 by omega,
    show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by omega,
    prod_eq_prod_Ico_succ_bot (by omega : 1 < j + 1 + 1) squareFactor,
    show squareFactor 1 = (X + 1) ^ 2 by simp [squareFactor], pow_succ]
  ring

end fibPiSquared_poly_eq_sum

open fibPiSquared_poly_eq_sum in
/-- **Explicit formula for the polynomials $p_n$.** Let $p_1, p_2, \dots$ be polynomials with
integer coefficients such that $p_1 = 1$ and, for every $n \ge 1$,
$p_{n+1}(x) = (2x + 2n + 1)(2x + 2n + 2)\, p_n(x) - (x + 1)^2 p_n(x + 1)$. Then for every
$n \ge 1$, as polynomials in $x$,

$$p_n(x) = \sum_{j=0}^{n-1} (-1)^j \binom{n-1}{j} \Bigl(\prod_{k=2j+3}^{2n} (2x + k)\Bigr)
\prod_{t=1}^{j} (x + t)^2.$$

Source: Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024), no. 1,
Lemma 2.4 (`fq-2024-tonien10292023-lem-2.4`). -/
public theorem fibPiSquared_poly_eq_sum (p : ℕ → ℤ[X]) (hp1 : p 1 = 1)
    (hp : ∀ n, 1 ≤ n → p (n + 1) = (2 * X + C (2 * n + 1 : ℤ)) * (2 * X + C (2 * n + 2 : ℤ)) *
      p n - (X + 1) ^ 2 * (p n).comp (X + 1))
    {n : ℕ} (hn : 1 ≤ n) :
    p n = ∑ j ∈ Finset.range n, (-1) ^ j * ((n - 1).choose j : ℤ[X]) *
      (∏ k ∈ Finset.Ico (2 * j + 3) (2 * n + 1), (2 * X + C (k : ℤ))) *
      ∏ t ∈ Finset.Icc 1 j, (X + C (t : ℤ)) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  clear hn
  suffices h : p (m + 1) = ∑ j ∈ range (m + 1), (m.choose j : ℤ[X]) * term (m + 1) j by
    simpa only [term, linearFactor, squareFactor, Nat.succ_sub_one, Ico_add_one_right_eq_Icc,
      map_natCast, mul_assoc, mul_left_comm, mul_comm] using h
  induction m with
  | zero => simpa [term] using hp1
  | succ m ih =>
    rw [hp (m + 1) (by omega), ih, Finset.sum_choose_succ_mul (fun j _ ↦ term (m + 2) j) m]
    simp only [Polynomial.sum_comp, mul_comp, natCast_comp, Finset.mul_sum, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    · refine sum_congr rfl fun j hj ↦ ?_
      rw [term_succ (mem_range.mp hj)]
      ring
    · refine sum_congr rfl fun j _ ↦ ?_
      rw [term_shift]
      ring

end MetaMathlibExt
