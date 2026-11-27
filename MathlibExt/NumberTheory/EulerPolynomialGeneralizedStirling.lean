/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.EulerPolynomialBinomialAverage
public import MathlibExt.NumberTheory.EulerPolynomialStirling
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.EulerPolynomialFormulasEulerPolyHalfEqSum

/-!
# Euler polynomials via generalized Stirling polynomials

The affine substitution `x ↦ 2x - 1` takes the expansion of `2^n E_n((x + 1)/2)` to
an expansion of `2^n E_n(x)`.

## References

* Nouara Mokhtari, Rachid Boumahdi, and Farid Bencherif,
  *Generalizations of Several Explicit Formulas for Euler Polynomials*, INTEGERS 25 (2025),
  Article A65, pp. 1–15, Theorem 4.2, equations (28)–(29). We use the half-argument expansion
  in their proof of Theorem 4.2, before expanding the coefficients from Lemma 2.2.
* Chun-Feng Wei and Feng Qi, *Several closed expressions for the Euler numbers*, Journal of
  Inequalities and Applications 2015 (2015), Article 219, Theorem 1.3, equation (1.5),
  the Euler-number formula that Theorem 4.2 generalizes.
-/

open Polynomial

namespace MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

@[expose] public section

/-- **Euler polynomials via generalized Stirling polynomials.** Let $E_n(x)$ denote the Euler
polynomial, $\alpha_k$ the Taylor coefficients of $(2 + 2z)/(2 + 2z + z^2)$, and
$S(n, k, x) = \frac{1}{k!} \sum_{j=0}^{k} \binom{k}{j} (-1)^{k-j} (x + j)^n$ the generalized
Stirling polynomial. For every integer $n \ge 1$, as polynomials in $x$ with rational
coefficients, $2^n E_n(x) = \sum_{k=0}^{n} k! \, \alpha_k \, S(n, k, 2x - 1)$.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Theorem 4.2. -/
theorem eulerPoly_eq_sum_genStirling (n : ℕ)
    (hn : 1 ≤ n) :
    (2 : ℚ) ^ n • eulerPoly n =
      ∑ k ∈ Finset.range (n + 1),
        ((Nat.factorial k : ℚ) * eulerAlpha k) •
          (genStirlingPoly n k).comp (C 2 * X - 1) := by
  -- Retain the source's positive-degree hypothesis; the half-argument identity needs no bound.
  have _ := hn
  have hcomp : (C (1 / 2 : ℚ) * (X + 1)).comp (C 2 * X - 1) = X := by
    simp only [mul_comp, C_comp, add_comp, X_comp, one_comp, sub_add_cancel]
    rw [← mul_assoc, ← C_mul]
    norm_num
  have h := congrArg (fun p : ℚ[X] => p.comp (C 2 * X - 1)) (eulerPoly_half_eq_sum n)
  simpa only [smul_comp, comp_assoc, hcomp, comp_X, sum_comp] using h

end

end MathlibExt.NumberTheory.EulerPolynomialFormulasWanted
