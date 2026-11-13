/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Manin's conjecture for the split D4 cubic surface (AIM rational points workshop, Problem 5)

AIM workshop Rational and integral points on higher dimensional varieties, Problem 5 (Y. Tschinkel):
for `xyz = t(x + y + z)²` with height `max(|x|, |y|, |z|, |t|)` on primitive integer points,
excluding the points on lines, prove a counting function `∼ c B (log B)⁶`. The list adds: this is a
singular cubic surface, so we also expect an explicit constant.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.D4CubicSurfaceManinCountAIMAlgebraicNumberTheoryProblem89Wanted

/-!
Source: AIM workshop Rational and integral points on higher dimensional varieties (2002), problem
list, https://aimath.org/WWN/qptsurface2/qptsurface2.pdf, Problem 5 (Y. Tschinkel). UnsolvedMath
record UM-20000437 (`AIM-ALGEBRAIC_NUMBER_THEORY-0089`), dataset ulamai/UnsolvedMath v1.8.0.

Points are primitive vectors `(x₀, x₁, x₂, x₃) ∈ ℤ⁴` with `x₀ (x₁ + x₂ + x₃)² = x₁ x₂ x₃` (the
source's `t = x₀`). The lines of the surface are `x₀ = xᵢ = 0` and `x₁ + x₂ + x₃ = xᵢ = 0` for `i =
1, 2, 3` (Le Boudec, introduction), and a point of the surface lies on one of them exactly when `x₁
x₂ x₃ = 0`, so the open set is `x₁ x₂ x₃ ≠ 0`. Each rational point is counted twice (`±x`), which
doubles the constant. `c > 0` is existential: the explicit constant the list expects (Le Boudec's
`c_{V,H}`, Peyre's constant) is not formalized, so the declaration is labeled `partial_scope`.
-/

/-- The number of primitive integer vectors `x = (x₀, x₁, x₂, x₃)` on the cubic surface
`x₀ (x₁ + x₂ + x₃)² = x₁ x₂ x₃` with `x₁ x₂ x₃ ≠ 0` (off the six lines of the surface) and
height `max |xᵢ| ≤ B`. Each rational point of the surface is counted twice (`±x`). -/
noncomputable def d4CubicPointCount (B : ℝ) : ℕ :=
  Set.ncard {x : Fin 4 → ℤ | (∀ k : ℤ, (∀ i, k ∣ x i) → IsUnit k) ∧
    x 0 * (x 1 + x 2 + x 3) ^ 2 = x 1 * x 2 * x 3 ∧ x 1 * x 2 * x 3 ≠ 0 ∧
    ∀ i, (|x i| : ℝ) ≤ B}

/-- Tschinkel's problem (AIM workshop Rational and integral points on higher dimensional
varieties, Problem 5): the counting function of the split `D₄` cubic surface
`x₀ (x₁ + x₂ + x₃)² = x₁ x₂ x₃`, with the six lines removed, satisfies `N(B) ∼ c B (log B)⁶`
for a constant `c > 0`. -/
def d4CubicManinAsymptotic : Prop :=
  ∃ c : ℝ, 0 < c ∧ Filter.Tendsto
    (fun B : ℝ => (d4CubicPointCount B : ℝ) / (c * B * Real.log B ^ 6)) Filter.atTop (nhds 1)

/--
Resolved true: Le Boudec proved Manin's conjecture for this split `D₄` cubic surface, `N_{U,H}(B) =
c B (log B)⁶ (1 + o(1))` with `c` Peyre's constant, answering Tschinkel's AIM problem; `c > 0` also
follows from Browning's lower bound `N_{U,H}(B) ≫ B (log B)⁶` recorded in the AIM list. Source: AIM
workshop Rational and integral points on higher dimensional varieties (2002), problem list,
https://aimath.org/WWN/qptsurface2/qptsurface2.pdf, Problem 5 (Y. Tschinkel); resolution: P. Le
Boudec, Affine congruences and rational points on a certain cubic surface, Algebra Number Theory 8
(2014), 1259-1296, arXiv:1207.2685, Theorem 1: N_{U,H}(B) = c_{V,H} B log(B)^6 (1 +
O(1/log(log(B))^{1/6})) for V: x0(x1 + x2 + x3)^2 = x1 x2 x3, U = V minus its six lines, H = max
|xi| on primitive vectors, with c_{V,H} Peyre's constant; the introduction states that this answers
the problem Tschinkel posed at the 2002 AIM workshop, after Browning's bounds N_{U,H}(B) ≍ B (log
B)^6, https://doi.org/10.2140/ant.2014.8.1259.
-/
public theorem_wanted d4CubicManinAsymptotic_holds : d4CubicManinAsymptotic

end MathlibExt.NumberTheory.D4CubicSurfaceManinCountAIMAlgebraicNumberTheoryProblem89Wanted
