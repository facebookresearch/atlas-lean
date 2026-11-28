/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import MathlibExt.NumberTheory.MultiplicativeAdditiveEightSquares
public import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquares
public import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquaresRigidity
public import MathlibExt.NumberTheory.MultiplicativeAdditiveThreePairedSquares
public import MathlibExt.NumberTheory.SixAndEightNonzeroSquares
public import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquaresMultiplicativeAdditivePairedSquaresEqIdOfThreeOrFour
public import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquaresMultiplicativeAdditivePairedSquaresDichotomy
public import MathlibExt.NumberTheory.MultiplicativeAdditiveSixSquares
public import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquaresSumNonzeroSquaresIffNotMemExceptional

namespace MetaMathlibExt

@[expose] public section

/-! # Multiplicative functions additive on partitions of `2k` nonzero squares

Statements from Mahajan's paper. Equation (1) of the paper is
`f(∑_{i=1}^{2k} x_i²) = ∑_{j=1}^{k} f(x_{2j-1}² + x_{2j}²)` for all positive integers
`x_1, …, x_{2k}`; it is written here with the pairs `(x_{2j-1}, x_{2j})` relabelled as
`(x j, y j)` for `j : Fin k`. Equation (2) is `k`-additivity on
`E₂ = {a² + b² : a, b ≥ 1}`. A multiplicative function `ℕ → ℂ` is an
`ArithmeticFunction ℂ` with `IsMultiplicative`; its value at `0` plays no role.
-/

open ArithmeticFunction

end

end MetaMathlibExt
