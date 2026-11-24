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
public import MathlibExt.NumberTheory.EllipticCurveNaiveHeightUnitCoeff

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

/-- **Height lower bounds on $y^2 = x^3 + ax + b$ when $b = \pm a$, $b = 0$ or $a = 0$.** Let
$a, b \in \mathbb{Z}$ with $4a^3 + 27b^2 \ne 0$, and for $u, v \in \mathbb{Q}$ let
$H(u, v) = \max(|U|, |V|, |W|)$, where $U, V, W$ are coprime integers with
$(U : V : W) = (u : v : 1)$. Consider the rational solutions $(u, v)$ of $v^2 = u^3 + au + b$.
(a) If $b = a$, every solution has $H(u, v) \ge (|a|/4)^{1/3}$.
(b) If $b = -a$, every solution with $H(u, v) < (|a|/4)^{1/3}$ is $(1, 1)$ or $(1, -1)$.
(c) If $b = 0$, every solution with $H(u, v) < (|a|/4)^{1/3}$ is $(0, 0)$.
(d) If $a = 0$, every solution has $H(u, v) \ge (|b|/3)^{1/3}$.

In (b) the points $(1, \pm 1)$ and the point at infinity need not form a subgroup of order
three: for $a = 5$, doubling $(1, 1)$ gives $(14, -53)$.

Source: Dimitrios Poulakis, *Lower Bounds for the Height of Rational Points of Elliptic
Curves*, INTEGERS 25 (2025), Article A66, Theorem 3 (`integers-2025-A66-thm-3`). -/
public theorem_wanted naiveHeight_lower_bound_of_special_coeff (a b : ℤ)
    (hE : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    (b = a → ∀ u v : ℚ, v ^ 2 = u ^ 3 + a * u + b →
        ¬ Height.mulHeight ![u, v, 1] < (|(a : ℝ)| / 4) ^ ((1 : ℝ) / 3)) ∧
      (b = -a → ∀ u v : ℚ, v ^ 2 = u ^ 3 + a * u + b →
        Height.mulHeight ![u, v, 1] < (|(a : ℝ)| / 4) ^ ((1 : ℝ) / 3) →
          u = 1 ∧ (v = 1 ∨ v = -1)) ∧
      (b = 0 → ∀ u v : ℚ, v ^ 2 = u ^ 3 + a * u + b →
        Height.mulHeight ![u, v, 1] < (|(a : ℝ)| / 4) ^ ((1 : ℝ) / 3) → u = 0 ∧ v = 0) ∧
      (a = 0 → ∀ u v : ℚ, v ^ 2 = u ^ 3 + a * u + b →
        ¬ Height.mulHeight ![u, v, 1] < (|(b : ℝ)| / 3) ^ ((1 : ℝ) / 3))

/-- **Height of a point on $y^2 = x^3 + ax - b$ versus the height of its $x$-coordinate.** Let
$a, b \in \mathbb{Z}$ with $a \ne 0$, $b > 0$ and $4a^3 + 27b^2 \ne 0$. For $u \in \mathbb{Q}$
let $H(u) = \max(|u_0|, u_1)$, where $u = u_0/u_1$ in lowest terms with $u_1 > 0$, and for
$u, v \in \mathbb{Q}$ let $H(u, v) = \max(|U|, |V|, |W|)$, where $U, V, W$ are coprime integers
with $(U : V : W) = (u : v : 1)$. Then every rational solution $(u, v)$ of
$v^2 = u^3 + au - b$ satisfies $H(u, v) < \sqrt{1 + |a|}\, H(u)^{3/2}$.

Source: Dimitrios Poulakis, *Lower Bounds for the Height of Rational Points of Elliptic
Curves*, INTEGERS 25 (2025), Article A66, Lemma 4 (`integers-2025-A66-lem-4`). -/
public theorem_wanted naiveHeight_lt_sqrt_mul_naiveHeight_x_rpow (a b : ℤ) (ha : a ≠ 0)
    (hb : 0 < b) (hE : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (u v : ℚ)
    (hP : v ^ 2 = u ^ 3 + a * u - b) :
    Height.mulHeight ![u, v, 1] <
      Real.sqrt (1 + |(a : ℝ)|) * Height.mulHeight ![u, 1] ^ ((3 : ℝ) / 2)

end

end MetaMathlibExt
