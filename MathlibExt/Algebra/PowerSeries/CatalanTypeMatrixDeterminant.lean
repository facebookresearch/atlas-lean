/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.LinearAlgebra.Matrix.Block
public import MathlibExt.Algebra.PowerSeries.UnifiedCatalanTypePolynomials

/-! # Determinant of the lower-triangular Catalan-type matrix -/

namespace MetaMathlibExt

open PowerSeries

/-- **Determinant of the lower-triangular Catalan-type matrix.** Let $m, N$ be natural numbers,
let $\lambda, x$ be real numbers, let $A$ be a polynomial with integer coefficients, and let
$P_n$ be the coefficient of $t^n$ in $(1 + A(x)\, t)(1 - m t + x t^m)^{-\lambda}$, where
$(1 - m t + x t^m)^{-\lambda}$ denotes the negative real power of the trinomial
$1 - m t + x t^m$ with exponent $\lambda$ as a power series in $t$ (for $m \ge 1$, its expansion
in powers of $t$). Then the $(N + 1) \times (N + 1)$ matrix whose $(i, j)$ entry, for
$0 \le i, j \le N$, is $P_{i-j}$ when $j \le i$ and $0$ otherwise has determinant $P_0^{N+1}$.

In the paper's notation $P_n = P^{\lambda,A}_{n,m}(x)$ (Definition 6 at $y = 0$) and the matrix
is $P_N^{(m,\lambda,A)}(x)$ of Equation (18). The paper's proviso $P_0 \ne 0$ is dropped.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 7
(`integers-2026-A105-thm-7`). -/
public theorem det_catalanTypeLowerTriangular (m N : ℕ) (lam x : ℝ)
    (A : Polynomial ℤ) :
    let P : ℕ → ℝ := fun n ↦
      coeff n ((1 + C (Polynomial.aeval x A) * X) * trinomialNegPowSeries lam 1 m x m)
    (Matrix.of fun i j : Fin (N + 1) ↦ if j ≤ i then P (i - j) else 0).det = P 0 ^ (N + 1) := by
  intro P
  rw [Matrix.det_of_isLowerTriangular]
  · simp [Matrix.of_apply]
  · intro i j hij
    change i < j at hij
    simp [Matrix.of_apply, not_le.mpr hij]

end MetaMathlibExt
