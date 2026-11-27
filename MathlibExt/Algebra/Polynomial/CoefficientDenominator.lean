/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Rat.Defs

/-!
# Denominators of rational polynomials

`polynomialDenominator P` is the least common multiple of the denominators of the coefficients
of `P : ℚ[X]`; it is `1` exactly when `P` has integer coefficients.

## Main definitions

* `MetaMathlibExt.polynomialDenominator`

## Main statements

* `MetaMathlibExt.coeff_den_dvd_polynomialDenominator`
* `MetaMathlibExt.polynomialDenominator_eq_one_iff`
-/

@[expose] public section

namespace MetaMathlibExt

open Polynomial

/-- **Denominator of a rational polynomial.** For a polynomial $P \in \mathbb{Q}[x]$, the
denominator $\operatorname{denom}(P)$ is the least common multiple of the denominators (in lowest
terms) of the nonzero coefficients of $P$; in particular $\operatorname{denom}(0) = 1$. Thus
$\operatorname{denom}(P) = 1$ exactly when $P \in \mathbb{Z}[x]$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 2 (notation
`denom`). -/
public def polynomialDenominator (P : ℚ[X]) : ℕ :=
  P.support.lcm fun i => (P.coeff i).den

/-- **Coefficient denominators divide the denominator of a polynomial.** For every polynomial
$P \in \mathbb{Q}[x]$ and every $i \in \mathbb{N}$, the denominator (in lowest terms) of the
coefficient of $x^i$ in $P$ divides the denominator $\operatorname{denom}(P)$ of $P$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 2
(definition of `denom`). -/
public theorem coeff_den_dvd_polynomialDenominator (P : ℚ[X]) (i : ℕ) :
    (P.coeff i).den ∣ polynomialDenominator P := by
  by_cases hi : i ∈ P.support
  · exact Finset.dvd_lcm hi
  · rw [Polynomial.notMem_support_iff.mp hi]
    simp

/-- **Denominator one characterizes integer polynomials.** For every polynomial
$P \in \mathbb{Q}[x]$, its denominator $\operatorname{denom}(P)$ equals $1$ if and only if, for
every $i \in \mathbb{N}$, the coefficient of $x^i$ in $P$ is an integer.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 1
(`denom(B_n(x)) > 1` is equivalent to `B_n(x) ∉ ℤ[x]`). -/
public theorem polynomialDenominator_eq_one_iff (P : ℚ[X]) :
    polynomialDenominator P = 1 ↔ ∀ i, (P.coeff i).den = 1 := by
  constructor
  · intro h i
    exact Nat.dvd_one.mp (h ▸ coeff_den_dvd_polynomialDenominator P i)
  · intro h
    exact Nat.dvd_one.mp (Finset.lcm_dvd fun i _ => (h i).symm ▸ dvd_refl 1)

end MetaMathlibExt
