/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

namespace MetaMathlibExt

/-- **Integrand of the antiderivative condition.** Let $S$ be a sequence of real polynomials
indexed by the natural numbers, with terms $S(l)$. For a natural number $l$ and a real number
$x$, the integrand is
$$\frac{8x^l - S(l)(x)}{\sqrt{x}\,(4 - x)},$$
where $\sqrt{x} = 0$ for $x < 0$ and a quotient with denominator $0$ is $0$.

Source: canonical name `polynomial T_{l-1}`, concept_id `jis_sem_267c1cca81c8b3a0062a0742`,
statement `jis_d5c7f2eca643e293a3405354`, source `jis_source_34b829866c2fa232064ad7c0`. -/
noncomputable def TIntegrand (S : ℕ → Polynomial ℝ) (l : ℕ) (x : ℝ) : ℝ :=
  (8 * x ^ l - Polynomial.aeval x (S l)) / (Real.sqrt x * (4 - x))

/-- **Polynomial family defined by an antiderivative.** Let $S$ and $T$ be sequences of real
polynomials indexed by the natural numbers, with terms $S(l)$ and $T(l)$. The pair $(S, T)$
satisfies this predicate when $T(0) = 0$; for every $l \ge 1$ the polynomial $T(l)$ is nonzero
and has degree $l - 1$; and for every $l \ge 1$ and every real $x$ with $0 < x < 4$, the function
$y \mapsto 2\sqrt{y}\,T(l)(y)$ is differentiable at $x$ with derivative
$$\frac{8x^l - S(l)(x)}{\sqrt{x}\,(4 - x)}.$$

The term $T(l)$ stands for the polynomial $T_{l-1}$ of the source, so $T(0) = 0$ encodes the
convention $T_{-1} = 0$, and the derivative condition expresses $T_{l-1}(x)$ as
$\frac{1}{2\sqrt{x}}$ times an antiderivative of the displayed integrand.

Source: canonical name `polynomial T_{l-1}`, concept_id `jis_sem_267c1cca81c8b3a0062a0742`,
statement `jis_d5c7f2eca643e293a3405354`, source `jis_source_34b829866c2fa232064ad7c0`. -/
def IsPolyTFamily (S T : ℕ → Polynomial ℝ) : Prop :=
  T 0 = 0 ∧
    (∀ l : ℕ, 1 ≤ l → (T l).natDegree = l - 1 ∧ T l ≠ 0) ∧
    ∀ l : ℕ, 1 ≤ l → ∀ x : ℝ, 0 < x → x < 4 →
      HasDerivAt (fun y : ℝ => 2 * Real.sqrt y * Polynomial.aeval y (T l))
        (TIntegrand S l x) x

end MetaMathlibExt
