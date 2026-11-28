/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Multiplicative functions additive on sums of two triangular numbers

Statements from Poo-Sung Park, "Multiplicative Functions Additive on
the Sums of Two Positive Triangular Numbers", *Journal of Integer
Sequences* 28 (2025), Article 25.4.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Park/park10.html>).

The paper's `T₂` is the set of sums of two positive triangular numbers.
Here that condition is written without division as
`2 * n = a * (a + 1) + b * (b + 1)` with `1 ≤ a` and `1 ≤ b`.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditive

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditiveWanted

end MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditiveWanted
