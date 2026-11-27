/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeAdditiveOnSquares

/-!
# Multiplicative functions additive on squares and on sums of consecutive squares

Statements from Elchin Hasanalizade, *On the k-Additive Uniqueness of Sums of Consecutive
Squares for Multiplicative Functions*, INTEGERS 25 (2025), Article A40. Multiplicative
functions are `ArithmeticFunction ℂ` with `IsMultiplicative` (which includes `f 1 = 1`).
The paper's set `T = {s_m - s_n : m > n ≥ 0}` with `s_n = ∑_{i=0}^{n} i²` is written as
the sums `∑ j ∈ Finset.Ioc n m, j ^ 2` with `n < m`.
-/
