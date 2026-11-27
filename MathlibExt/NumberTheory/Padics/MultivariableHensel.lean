/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.Hensel
import MathlibExt.Algebra.MvPolynomial.Stable

/-!
# Multivariable Hensel lemma over the p-adic integers

A polynomial with a sufficiently small value relative to one partial derivative has a zero
obtained by varying only the corresponding coordinate.
-/

namespace MetaMathlibExt

open MvPolynomial

/-- **Multivariable Hensel lemma over the p-adic integers.** Let $p$ be a prime, let
$f \in \mathbb{Z}_p[x_1, \dots, x_n]$ and $a \in \mathbb{Z}_p^n$, and suppose that for some index
$i$ the $p$-adic absolute values satisfy $|f(a)|_p < |(\partial f / \partial x_i)(a)|_p^2$, that
is, $\operatorname{ord}_p f(a) > 2 \operatorname{ord}_p (\partial f / \partial x_i)(a)$. Then
there is a point $x \in \mathbb{Z}_p^n$ with $f(x) = 0$.

Source: Renz Jimwel Mina and Jerico Bacani, *Rank of the Elliptic Curve y^2=x^3-2pqx*,
INTEGERS 26 (2026), Article A51, Lemma 1 (`integers-2026-A51-lem-1`), quoted there as Hensel's
lemma. -/
public theorem exists_mvPolynomial_eval_eq_zero_of_norm_lt_norm_pderiv_sq
    {p : ℕ} [Fact p.Prime] {n : ℕ} (f : MvPolynomial (Fin n) ℤ_[p]) (a : Fin n → ℤ_[p])
    (i : Fin n)
    (h : ‖MvPolynomial.eval a f‖ < ‖MvPolynomial.eval a (MvPolynomial.pderiv i f)‖ ^ 2) :
    ∃ x : Fin n → ℤ_[p], MvPolynomial.eval x f = 0 := by
  let g := univariateSpecialization i a f
  have hg : ‖g.aeval (a i)‖ < ‖g.derivative.aeval (a i)‖ ^ 2 := by
    simpa only [g, Polynomial.coe_aeval_eq_eval, ← derivative_univariateSpecialization,
      eval_univariateSpecialization, Function.update_eq_self] using h
  obtain ⟨z, hz, _⟩ := hensels_lemma hg
  refine ⟨Function.update a i z, ?_⟩
  rw [← eval_univariateSpecialization]
  exact hz

end MetaMathlibExt
