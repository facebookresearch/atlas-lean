/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Resultant identity for pairwise sums

The resultant is taken in the outer variable of a polynomial over `K[X]`.
-/

namespace MetaMathlibExt

open Polynomial

/-- **Resultant identity for pairwise sums.** Let $K$ be a field of characteristic $0$, let
$m, n \ge 0$ be integers, and let $\alpha_1, \dots, \alpha_m$ and $\beta_1, \dots, \beta_n$ be
elements of $K$. Regard $f(y) = \prod_{i=1}^{m} (1 - y - \alpha_i x)$ and
$g(y) = \prod_{j=1}^{n} (y - \beta_j x)$ as polynomials in $y$ with coefficients in $K[x]$,
and let $\operatorname{Res}_{m,n}(f, g)$ be the determinant of their Sylvester matrix formed with
the formal degrees $m$ and $n$. Then in $K[x]$

$$
\prod_{i=1}^{m} \prod_{j=1}^{n} \bigl(1 - (\alpha_i + \beta_j)x\bigr)
= (-1)^{mn} \operatorname{Res}_{m,n}(f, g).
$$

With $U(x) = \prod_{i=1}^{m} (1 - \alpha_i x)$ and $V(x) = \prod_{j=1}^{n} (1 - \beta_j x)$, these
are $f(y) = (1 - y)^m U(x / (1 - y))$ and $g(y) = y^n V(x / y)$, the form used in the source.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 10 (`jis-2024-24.1.3-thm-10`). -/
public theorem prod_one_sub_add_eq_resultant {K : Type*} [Field K] [CharZero K] (m n : ℕ)
    (α : Fin m → K) (β : Fin n → K) :
    ∏ i, ∏ j, (1 - Polynomial.C (α i + β j) * Polynomial.X) =
      (-1) ^ (m * n) * Polynomial.resultant
        (∏ i, (1 - Polynomial.X - Polynomial.C (Polynomial.C (α i) * Polynomial.X)))
        (∏ j, (Polynomial.X - Polynomial.C (Polynomial.C (β j) * Polynomial.X))) m n := by
  let f : K[X][X] := ∏ i, (1 - X - C (C (α i) * X))
  have hlin : (1 - X : K[X][X]).natDegree = 1 := by
    rw [natDegree_sub_eq_right_of_natDegree_lt (by simp), natDegree_X]
  have hf : f.natDegree ≤ m := by
    apply (natDegree_prod_le Finset.univ (fun i ↦ (1 - X - C (C (α i) * X) : K[X][X]))).trans
    simp only [natDegree_sub_C, hlin, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one, le_refl]
  let g (j : Fin n) : K[X][X] := X - C (C (β j) * X)
  have hg : (∏ j, g j).natDegree = n := by
    simp only [g, natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, Fintype.card_fin]
  -- Evaluate the reversed resultant at the roots of the monic linear factors.
  have hres := resultant_prod_left Finset.univ g f m (by simp [g, -map_mul]) hf
  rw [hg] at hres
  simp only [g, natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ hf] at hres
  rw [Nat.mul_comm m n, ← resultant_comm, hres, Finset.prod_comm]
  simp only [f, eval_prod, eval_sub, eval_one, eval_X, eval_C, map_add, add_mul]
  simp only [sub_sub, add_comm]

end MetaMathlibExt
