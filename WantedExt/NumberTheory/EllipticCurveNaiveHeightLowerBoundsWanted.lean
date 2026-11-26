/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.NumberField
public import MathlibExt.NumberTheory.EllipticCurveNaiveHeightLowerBounds
public import MathlibExt.NumberTheory.EllipticCurveNaiveHeightSpecialCoeff
public import MathlibExt.NumberTheory.EllipticCurveNaiveHeightUnitCoeff
public import MathlibExt.NumberTheory.EllipticCurveNaiveHeightLowerBoundsNaiveHeightLtSqrtMulNaiveHeightXRpow

/-!
# Lower bounds for the naive height of rational points on elliptic curves

Statements from Dimitrios Poulakis, *Lower Bounds for the Height of Rational Points of Elliptic
Curves*, INTEGERS 25 (2025), Article A66.

The curves are `E : y² = x³ + ax + b` with `a, b ∈ ℤ` and `4a³ + 27b² ≠ 0`; a point
`P ∈ E(ℚ) \ {O}` is a pair `(u, v) ∈ ℚ²` on the curve. The naive height of an affine point
`Q = (b₁, …, bₙ)` is `H(Q) = H(b₁ : ⋯ : bₙ : 1)`, the maximum of the absolute values of a
primitive integer representative; here it is Mathlib's `Height.mulHeight ![b₁, …, bₙ, 1]`, so
`H(P) = Height.mulHeight ![u, v, 1]` and `H(x(P)) = Height.mulHeight ![u, 1]`. For
`p(x, y) = y² - x³ - ax - b`, `‖p‖ = √(2 + a² + b²)` is the Euclidean norm of its coefficients.
-/

namespace MetaMathlibExt

@[expose] public section

end

end MetaMathlibExt
