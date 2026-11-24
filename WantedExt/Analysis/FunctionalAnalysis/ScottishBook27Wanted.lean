/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook27Wanted

/-- **Continuous polynomial functions on a complex normed space.** Let $E$ be a complex normed
space. A function $F : E \to \mathbb{C}$ is a continuous polynomial function if there are a
natural number $n$, natural numbers $m_1, \dots, m_n$ and continuous $\mathbb{C}$-multilinear
maps $A_i : E^{m_i} \to \mathbb{C}$, with $A_i$ taking $m_i$ arguments, such that
$F(x) = \sum_{i=1}^{n} A_i(x, \dots, x)$ for every $x \in E$.

A $0$-multilinear map is a constant, so constant functions are polynomial functions. -/
def IsPolynomialOn (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → ℂ) : Prop :=
  ∃ (n : ℕ) (m : Fin n → ℕ)
    (A : (i : Fin n) → (E [× m i]→L[ℂ] ℂ)),
    ∀ x, F x = ∑ i, A i fun _ => x

/--
**Bezout identity for polynomials without a common zero.** Let $E$ be a complex Banach space
and let $F, G : E \to \mathbb{C}$ be continuous polynomial functions with no common zero, that
is, $G(x) \neq 0$ whenever $F(x) = 0$. Then there are continuous polynomial functions
$\varphi, \psi : E \to \mathbb{C}$ such that $F(x) \varphi(x) + G(x) \psi(x) = 1$ for every
$x \in E$.

This is the identity recorded in the addendum to Problem 27 of the Scottish Book (Mazur-Orlicz,
4 April 1939). The problem asks whether two complex polynomials on a complex Banach space that
both tend to $0$ along a sequence $(x_n)$ in the unit ball must have a common zero. The answer
is positive and follows from the identity by contradiction: continuous polynomials are bounded
on the unit ball, so $F(x_n) \varphi(x_n) + G(x_n) \psi(x_n)$ would tend to $0$, yet it equals
$1$.

Source: S. Mazur and W. Orlicz, Problem 27 of the Scottish Book, with the
positive answer via the Bezout identity in the addendum; see the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted bezout_identity_for_polynomials_without_common_zero :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      (F G : E → ℂ),
      IsPolynomialOn E F → IsPolynomialOn E G →
      (∀ x, F x = 0 → G x ≠ 0) →
      ∃ (φ ψ : E → ℂ), IsPolynomialOn E φ ∧ IsPolynomialOn E ψ ∧
        ∀ x, F x * φ x + G x * ψ x = 1

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook27Wanted
