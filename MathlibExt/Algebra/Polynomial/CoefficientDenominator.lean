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

/-- The denominator `denom(P)` of a rational polynomial: the least common multiple of the
denominators of its coefficients, so `denom(P) = 1` exactly when `P ∈ ℤ[x]`.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 2 (notation
`denom`). -/
public def polynomialDenominator (P : ℚ[X]) : ℕ :=
  P.support.lcm fun i => (P.coeff i).den

/-- Every coefficient denominator divides `polynomialDenominator P`.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 2
(definition of `denom`). -/
public theorem coeff_den_dvd_polynomialDenominator (P : ℚ[X]) (i : ℕ) :
    (P.coeff i).den ∣ polynomialDenominator P := by
  by_cases hi : i ∈ P.support
  · exact Finset.dvd_lcm hi
  · rw [Polynomial.notMem_support_iff.mp hi]
    simp

/-- `polynomialDenominator P = 1` exactly when every coefficient of `P` is an integer.

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
