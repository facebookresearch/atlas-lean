/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
public import MathlibExt.NumberTheory.GibonacciPolynomialInverseRatio
public import MathlibExt.NumberTheory.GibonacciPolynomialOddRatioSum
public import MathlibExt.NumberTheory.GibonacciPolynomialSquareSum
public import MathlibExt.NumberTheory.GibonacciPolynomialSquareSumsRevisited

/-!
# More sums involving gibonacci polynomial squares, revisited (statements)

Statements from Thomas Koshy, *More Sums Involving Gibonacci Polynomial Squares Revisited*,
The Fibonacci Quarterly 62 (2024), Article koshy07202023.

The Fibonacci polynomials `f_n(x)` (`f_0 = 0`, `f_1 = 1`) and Lucas polynomials `l_n(x)`
(`l_0 = 2`, `l_1 = x`), both with `g_{n+2} = x g_{n+1} + g_n`, are the existing
`generalizedFibonacciPolynomial` sequences over `ℤ[X]`, evaluated at a real `x` with
`Polynomial.aeval`; `Δ = √(x² + 4)`, `α = (x + Δ)/2`, `β = (x - Δ)/2`.

The paper takes `x` to be an arbitrary integer, but every statement rests on
`g_{m+r}/g_m → α^r`, which needs `x > 0`: at `x = -1`, `f_n(-1) = (-1)^{n+1} F_n` and the
Lemma 2.1 sum with `k = r = λ = 1` equals `(√5 - 1)/2`, not `f_2/f_1 - α = -(1 + √5)/2`. The
statement `tsum_fib_mul_div_gibonacciPoly_shift_sq_add`, now proved in
`MathlibExt.NumberTheory.GibonacciPolynomialSquareSumsRevisited`, takes a real `x > 0`.
Infinite sums start at `n = 1` in the paper and at `n = 0` there (index shifted by one).
-/

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- The Fibonacci polynomials `f_n(x)`. -/
local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1

/-- The Lucas polynomials `l_n(x)`. -/
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

end

end MetaMathlibExt
