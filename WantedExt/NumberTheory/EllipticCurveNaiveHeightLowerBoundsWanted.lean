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

/-- **Theorem 2.** On `y² = x³ + ax + b` (`a, b ∈ ℤ`, `4a³ + 27b² ≠ 0`):
(a) if `a = ±1` and `b ∉ {0, ±1}`, no point `P ∈ E(ℚ) \ {O}` has `H(P) < (|b|/5)^{1/3}`;
(b) if `a ∉ {0, ±1}` and `b = -1`, no point `P ∈ E(ℚ) \ {O}` has `H(P) < (|a|/5)^{1/3}`;
(c) if `a ∉ {0, ±1}` and `b = 1`, the only points `P ∈ E(ℚ) \ {O}` with
`H(P) < (|a|/5)^{1/3}` are `(0, ±1)`.

Source: Dimitrios Poulakis, *Lower Bounds for the Height of Rational Points of Elliptic
Curves*, INTEGERS 25 (2025), Article A66, Theorem 2 (`integers-2025-A66-thm-2`). -/
public theorem_wanted naiveHeight_lower_bound_of_unit_coeff (a b : ℤ)
    (hE : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    ((a = 1 ∨ a = -1) → b ≠ 0 → b ≠ 1 → b ≠ -1 → ∀ u v : ℚ, v ^ 2 = u ^ 3 + a * u + b →
        ¬ Height.mulHeight ![u, v, 1] < (|(b : ℝ)| / 5) ^ ((1 : ℝ) / 3)) ∧
      (a ≠ 0 → a ≠ 1 → a ≠ -1 → b = -1 → ∀ u v : ℚ, v ^ 2 = u ^ 3 + a * u + b →
        ¬ Height.mulHeight ![u, v, 1] < (|(a : ℝ)| / 5) ^ ((1 : ℝ) / 3)) ∧
      (a ≠ 0 → a ≠ 1 → a ≠ -1 → b = 1 → ∀ u v : ℚ, v ^ 2 = u ^ 3 + a * u + b →
        Height.mulHeight ![u, v, 1] < (|(a : ℝ)| / 5) ^ ((1 : ℝ) / 3) →
          u = 0 ∧ (v = 1 ∨ v = -1))

/-- **Theorem 3.** On `y² = x³ + ax + b` (`a, b ∈ ℤ`, `4a³ + 27b² ≠ 0`):
(a) if `b = a`, no point `P ∈ E(ℚ) \ {O}` has `H(P) < (|a|/4)^{1/3}`;
(b) if `b = -a`, the only affine points with `H(P) < (|a|/4)^{1/3}` are `(1, ±1)`;
(c) if `b = 0`, the only point `P ∈ E(ℚ) \ {O}` with `H(P) < (|a|/4)^{1/3}` is `(0, 0)`;
(d) if `a = 0`, no point `P ∈ E(ℚ) \ {O}` has `H(P) < (|b|/3)^{1/3}`.
The remark in (b) that `O` and `(1, ±1)` form a subgroup of order three is omitted: it fails
for `a = 5`, where `2 · (1, 1) = (14, -53)`.

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

/-- **Lemma 4.** On `y² = x³ + ax - b` with `a, b ∈ ℤ`, `a ≠ 0`, `b > 0` (and
`4a³ + 27b² ≠ 0`), every `P ∈ E(ℚ) \ {O}` satisfies `H(P) < √(1 + |a|) · H(x(P))^{3/2}`.

Source: Dimitrios Poulakis, *Lower Bounds for the Height of Rational Points of Elliptic
Curves*, INTEGERS 25 (2025), Article A66, Lemma 4 (`integers-2025-A66-lem-4`). -/
public theorem_wanted naiveHeight_lt_sqrt_mul_naiveHeight_x_rpow (a b : ℤ) (ha : a ≠ 0)
    (hb : 0 < b) (hE : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (u v : ℚ)
    (hP : v ^ 2 = u ^ 3 + a * u - b) :
    Height.mulHeight ![u, v, 1] <
      Real.sqrt (1 + |(a : ℝ)|) * Height.mulHeight ![u, 1] ^ ((3 : ℝ) / 2)

/-- **Corollary 1.** On `y² = x³ + ax + b` with `a, b ∈ ℤ`, `ab ≠ 0` (and `4a³ + 27b² ≠ 0`),
if `1 + |a| < ‖p‖^{1/2} / 1.782` then every `P ∈ E(ℚ) \ {O}` with `x(P) y(P) ≠ 0` satisfies
`H(P) > ‖p‖^{1/6} / 1.634`, where `‖p‖ = √(2 + a² + b²)`.

Source: Dimitrios Poulakis, *Lower Bounds for the Height of Rational Points of Elliptic
Curves*, INTEGERS 25 (2025), Article A66, Corollary 1 (`integers-2025-A66-cor-1`). -/
public theorem_wanted naiveHeight_gt_of_small_linear_coeff (a b : ℤ) (hab : a * b ≠ 0)
    (hE : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (hsmall : 1 + |(a : ℝ)| < Real.sqrt (2 + a ^ 2 + b ^ 2) ^ ((1 : ℝ) / 2) / 1.782) (u v : ℚ)
    (huv : u * v ≠ 0) (hP : v ^ 2 = u ^ 3 + a * u + b) :
    Real.sqrt (2 + a ^ 2 + b ^ 2) ^ ((1 : ℝ) / 6) / 1.634 < Height.mulHeight ![u, v, 1]

end

end MetaMathlibExt
