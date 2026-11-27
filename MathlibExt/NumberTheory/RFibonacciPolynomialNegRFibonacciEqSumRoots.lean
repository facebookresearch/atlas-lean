/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Lagrange
public import MathlibExt.NumberTheory.NegRFibonacciPolynomial
import Mathlib.Tactic.LinearCombination

/-!
# Binet formula for the negative-order Fibonacci polynomials

This module proves the sum over distinct roots for the (-r)-Fibonacci polynomials.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 9 (`integers-2025-A38-thm-9`).
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

private def rootMoment {K : Type*} [Field K] {r : ℕ}
    (β : Fin (r + 1) → K) (m : ℕ) : K :=
  ∑ k, β k ^ m / ∏ j ∈ Finset.univ.erase k, (β k - β j)

private lemma rootMoment_initial {K : Type*} [Field K] {r : ℕ}
    (β : Fin (r + 1) → K) (hβ : Function.Injective β) (m : ℕ) (hm : m ≤ r) :
    rootMoment β m = if m = r then 1 else 0 := by
  have h := Lagrange.coeff_eq_sum (s := Finset.univ) hβ.injOn
    (P := (X : K[X]) ^ m) (by
      simpa only [degree_X_pow, Finset.card_univ, Fintype.card_fin, Nat.cast_withBot,
        WithBot.coe_lt_coe] using (Nat.lt_succ_of_le hm))
  simpa [rootMoment, coeff_X_pow, eq_comm] using h.symm

private lemma root_equation {K : Type*} [Field K] {r : ℕ} (x : K) (y : Kˣ)
    (β : Fin (r + 1) → K)
    (hP : (X ^ (r + 1) - C (↑y⁻¹ : K) * X + C (x * ↑y⁻¹) : K[X]) =
      ∏ k, (X - C (β k))) (k : Fin (r + 1)) :
    β k ^ (r + 1) = (↑y⁻¹ : K) * β k - x * ↑y⁻¹ := by
  have h := congrArg (fun p : K[X] => p.eval (β k)) hP
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_prod] at h
  rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp)] at h
  linear_combination h

private lemma root_denominator {K : Type*} [Field K] {r : ℕ} (x : K) (y : Kˣ)
    (β : Fin (r + 1) → K)
    (hP : (X ^ (r + 1) - C (↑y⁻¹ : K) * X + C (x * ↑y⁻¹) : K[X]) =
      ∏ k, (X - C (β k))) (k : Fin (r + 1)) :
    (r : K) * β k ^ (r + 1) - x * ↑y⁻¹ =
      β k * ∏ j ∈ Finset.univ.erase k, (β k - β j) := by
  have h := Lagrange.eval_nodal_derivative_eval_node_eq
    (s := Finset.univ) (v := β) (Finset.mem_univ k)
  rw [Lagrange.nodal, ← hP] at h
  have hd : ((r : K) + 1) * β k ^ r - ↑y⁻¹ =
      ∏ j ∈ Finset.univ.erase k, (β k - β j) := by
    simpa [derivative_add, derivative_sub, derivative_pow_succ, Lagrange.eval_nodal] using h
  have he := root_equation x y β hP k
  rw [← hd]
  simp only [Units.val_inv_eq_inv_val] at he ⊢
  rw [pow_succ] at he ⊢
  linear_combination -he

private lemma rootMoment_recurrence {K : Type*} [Field K] {r : ℕ} (x : K) (y : Kˣ)
    (β : Fin (r + 1) → K)
    (hP : (X ^ (r + 1) - C (↑y⁻¹ : K) * X + C (x * ↑y⁻¹) : K[X]) =
      ∏ k, (X - C (β k))) (m : ℕ) :
    rootMoment β (m + r + 1) = ↑y⁻¹ * rootMoment β (m + 1) -
      x * ↑y⁻¹ * rootMoment β m := by
  simp only [rootMoment, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [show m + r + 1 = m + (r + 1) by omega, pow_add,
    root_equation x y β hP k, pow_succ]
  ring

private lemma negRFibonacci_eq_rootMoment {K : Type*} [Field K] {r : ℕ} (hr : 2 ≤ r)
    (x : K) (y : Kˣ) (β : Fin (r + 1) → K) (hβ : Function.Injective β)
    (hP : (X ^ (r + 1) - C (↑y⁻¹ : K) * X + C (x * ↑y⁻¹) : K[X]) =
      ∏ k, (X - C (β k))) (n : ℕ) :
    negRFibonacci r x y (n + 1) = rootMoment β (n + r) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n = 0
    · subst n
      simp [negRFibonacci_one, rootMoment_initial β hβ r (le_refl r)]
    · have hn' : 1 ≤ n := by omega
      have hrec := rootMoment_recurrence x y β hP (n - 1)
      rw [show n - 1 + r + 1 = n + r by omega,
        show n - 1 + 1 = n by omega] at hrec
      rw [hrec]
      by_cases hnr : n < r
      · rw [negRFibonacci_succ_of_lt x y hn' hnr,
          rootMoment_initial β hβ n (by omega),
          rootMoment_initial β hβ (n - 1) (by omega)]
        simp [show n ≠ r by omega, show n - 1 ≠ r by omega]
      · have hnr' : r ≤ n := by omega
        rw [negRFibonacci_succ_of_le x y (by omega) hnr',
          ih (n - r) (by omega), show n - r + r = n by omega]
        by_cases heq : n = r
        · subst n
          simp [rootMoment_initial β hβ (r - 1) (by omega),
            show r - 1 ≠ r by omega, negRFibonacci_zero]
        · rw [show n - r = (n - r - 1) + 1 by omega,
            ih (n - r - 1) (by omega), show n - r - 1 + r = n - 1 by omega]
          ring

/-- **Binet formula for the (-r)-Fibonacci polynomials.** Let $K$ be a field, $r \ge 2$,
$x \in K$ and $y \in K$ nonzero, and write $U_n = U^{(-r)}_n(x, y)$. Suppose that
$\beta_0, \dots, \beta_r \in K$ are pairwise distinct and that
$t^{r+1} - y^{-1} t + x y^{-1} = \prod_{k=0}^{r} (t - \beta_k)$ as polynomials over $K$. Then for
every $n \ge 0$,
$$U_{n+1} = \sum_{k=0}^{r} \frac{\beta_k^{n+r+1}}{r \beta_k^{r+1} - x y^{-1}},$$
where a term whose denominator vanishes is read as $0$.

The paper's hypothesis $x \ne \frac{r}{r+1} ((r+1) y)^{-1/r}$ is replaced by the distinctness of
the zeros (compare Lemma 1).

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 9 (`integers-2025-A38-thm-9`). -/
public theorem negRFibonacci_eq_sum_roots {K : Type*} [Field K] {r : ℕ} (hr : 2 ≤ r)
    (x : K) (y : Kˣ) (β : Fin (r + 1) → K) (hβ : Function.Injective β)
    (hP : (Polynomial.X ^ (r + 1) - Polynomial.C (↑y⁻¹ : K) * Polynomial.X
      + Polynomial.C (x * ↑y⁻¹) : Polynomial K) = ∏ k, (Polynomial.X - Polynomial.C (β k)))
    (n : ℕ) :
    negRFibonacci r x y (n + 1) = ∑ k, β k ^ (n + r + 1) / (r * β k ^ (r + 1) - x * ↑y⁻¹)
    := by
  rw [negRFibonacci_eq_rootMoment hr x y β hβ hP]
  unfold rootMoment
  apply Finset.sum_congr rfl
  intro k _
  rw [root_denominator x y β hP k]
  by_cases hk : β k = 0
  · simp [hk, show r ≠ 0 by omega]
  · rw [pow_succ, mul_comm (β k), mul_div_mul_right _ _ hk]

end

end MetaMathlibExt
