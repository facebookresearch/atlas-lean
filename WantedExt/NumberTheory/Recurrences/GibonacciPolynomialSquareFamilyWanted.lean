/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sums involving a family of gibonacci polynomial squares

Statements from Thomas Koshy, *Sums Involving a Family of Gibonacci Polynomial Squares:
Generalizations*, The Fibonacci Quarterly 62 (2024), Article koshy11112023. The theorem
`hasSum_fibPoly_sq_family` is proved in
`MathlibExt.NumberTheory.Recurrences.GibonacciPolynomialSquareFamilyHasSumFibPolySqFamily`.
The theorem `hasSum_lucasPoly_sq_family` is proved in
`MathlibExt.NumberTheory.Recurrences.LucasPolynomialSquareFamily`.

The Fibonacci polynomials `f_n(x)` (`f_0 = 0`, `f_1 = 1`) and Lucas polynomials `l_n(x)`
(`l_0 = 2`, `l_1 = x`), both with `z_{n+2} = x z_{n+1} + z_n`, are the existing
`generalizedFibonacciPolynomial` sequences over `ℤ[X]`, evaluated at a real `x` with
`Polynomial.aeval`; `g_n` is `f_n` or `l_n`, `Δ = √(x² + 4)` and `α = (x + Δ)/2`. The paper takes
`x` an arbitrary integer; the statements need `x > 0`: at `x = 0` the denominators `f_{2m}(0)`
vanish, and for `x < 0` the ratio `g_{m+r}/g_m` tends to `((x - Δ)/2)^r`, not `α^r`
(`x = -1`, `k = p = r = t = λ = 1`, `g = f`: the sum in Lemma 2.1 is `(√5 - 1)/2`, the right side
`-(1 + √5)/2`). They are stated for real `x > 0`, which contains the positive integers.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
public import MathlibExt.NumberTheory.Recurrences.GibonacciPolynomialRatioTelescoping
public import MathlibExt.NumberTheory.Recurrences.GibonacciPolynomialSquareFamilyHasSumFibPolySqFamily
public import MathlibExt.NumberTheory.Recurrences.LucasPolynomialSquareFamily

namespace MetaMathlibExt

open Polynomial

@[expose] public section

end

end MetaMathlibExt
