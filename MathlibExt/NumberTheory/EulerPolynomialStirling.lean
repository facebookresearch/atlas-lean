/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic.Ring

/-!
# Generalized Stirling polynomials and the coefficients `α_k`

For natural numbers `n` and `k`, `genStirlingPoly n k` is the generalized Stirling polynomial.
For each `k`, `eulerAlpha k` is the coefficient of `z^k` in `(2 + 2z) / (2 + 2z + z²)`.

## References

* Nouara Mokhtari, Rachid Boumahdi, and Farid Bencherif,
  *Generalizations of Several Explicit Formulas for Euler Polynomials*, INTEGERS 25 (2025),
  Article A65, pp. 1–15, Proposition 3.1 and Lemma 2.2.
-/

set_option autoImplicit false

@[expose] public section

open Polynomial

namespace MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

/-- **Generalized Stirling polynomial.** For natural numbers $n$ and $k$, the generalized
Stirling polynomial $S(n, k, x)$ is the polynomial in $x$ with rational coefficients
$$S(n, k, x) = \frac{1}{k!} \sum_{j=0}^{k} \binom{k}{j} (-1)^{k-j} (x + j)^n.$$

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Proposition 3.1 (definition). -/
noncomputable def genStirlingPoly (n k : ℕ) : ℚ[X] :=
  (1 / (Nat.factorial k : ℚ)) •
    ∑ j ∈ Finset.range (k + 1),
      ((Nat.choose k j : ℚ) * (-1) ^ (k - j)) •
        (X + C (j : ℚ)) ^ n

/-- **Taylor coefficients of (2 + 2z)/(2 + 2z + z²).** The rational numbers $\alpha_k$,
$k \ge 0$, are defined by $\alpha_0 = 1$, $\alpha_1 = 0$ and
$2\alpha_{k+2} + 2\alpha_{k+1} + \alpha_k = 0$ for every $k \ge 0$. They are the Taylor
coefficients of $(2 + 2z)/(2 + 2z + z^2)$ at $z = 0$.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Lemma 2.2 (generating function). -/
def eulerAlpha : ℕ → ℚ
  | 0 => 1
  | 1 => 0
  | k + 2 => -eulerAlpha (k + 1) - eulerAlpha k / 2

/-- Evaluating a generalized Stirling polynomial gives its defining finite sum at `x`. -/
theorem genStirlingPoly_eval (n k : ℕ) (x : ℚ) :
    (genStirlingPoly n k).eval x =
      (1 / (Nat.factorial k : ℚ)) *
        ∑ j ∈ Finset.range (k + 1),
          ((Nat.choose k j : ℚ) * (-1) ^ (k - j)) * (x + j) ^ n := by
  simp [genStirlingPoly, eval_finsetSum, eval_smul, smul_eq_mul]

/-- The Taylor coefficient $\alpha_0$ of $(2 + 2z)/(2 + 2z + z^2)$ is $1$. -/
theorem eulerAlpha_zero : eulerAlpha 0 = 1 := rfl

/-- The Taylor coefficient $\alpha_1$ of $(2 + 2z)/(2 + 2z + z^2)$ is $0$. -/
theorem eulerAlpha_one : eulerAlpha 1 = 0 := rfl

private theorem eulerAlpha_succ_succ (k : ℕ) :
    eulerAlpha (k + 2) = -eulerAlpha (k + 1) - eulerAlpha k / 2 := rfl

/-- The Taylor coefficients $\alpha_k$ of $(2 + 2z)/(2 + 2z + z^2)$ satisfy
$2\alpha_{k+2} + 2\alpha_{k+1} + \alpha_k = 0$ for every $k \ge 0$. -/
theorem eulerAlpha_rec (k : ℕ) :
    2 * eulerAlpha (k + 2) + 2 * eulerAlpha (k + 1) + eulerAlpha k = 0 := by
  rw [eulerAlpha_succ_succ]
  ring

end MathlibExt.NumberTheory.EulerPolynomialFormulasWanted
