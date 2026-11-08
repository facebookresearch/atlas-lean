/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.Analysis.Calculus.ScottishBook44Wanted

/-- A straight line through `(x₀, y₀, f x₀ y₀)` with direction `(u, v, w)`
lies entirely in the graph of `f`: the line has a nonzero horizontal
direction, and every point of the line satisfies the graph equation. -/
def LineInGraph (f : ℝ → ℝ → ℝ) (x₀ y₀ u v w : ℝ) : Prop :=
  ¬ (u = 0 ∧ v = 0) ∧
    ∀ t : ℝ, f (x₀ + t * u) (y₀ + t * v) = f x₀ y₀ + t * w

/-- Through every point of the graph of `f` pass two distinct lines lying
entirely in the graph: the two lines have non-proportional horizontal
directions, so they are distinct as sets. -/
def DoublyRuledGraph (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x₀ y₀ : ℝ, ∃ u₁ v₁ w₁ u₂ v₂ w₂ : ℝ,
    LineInGraph f x₀ y₀ u₁ v₁ w₁ ∧ LineInGraph f x₀ y₀ u₂ v₂ w₂ ∧
    ¬ ∃ c : ℝ, u₂ = c * u₁ ∧ v₂ = c * v₁

/--
Steinhaus, Problem 44 of the Scottish Book. Original question: let
`z = f(x, y)` be a continuous function whose graph is a surface through
every point of which there pass two straight lines lying entirely in the
surface; is the surface then necessarily a hyperbolic paraboloid, and can
this be proved without assuming continuity? The answer is affirmative in
both respects: Banach solved it, also without assuming continuity, with a
proof based on the remark that any two lines on the surface either
intersect or their projections on the `xy`-plane are parallel. The
conclusion is stated as the quadratic classification: `f` is a quadratic
polynomial, and either its quadratic part vanishes (the graph is a plane,
the degenerate doubly ruled case) or its discriminant is positive (the
graph is a hyperbolic paraboloid). No continuity of `f` is assumed.
Source: H. Steinhaus, Problem 44 of the Scottish Book; addendum in the
Scottish Book, 30 July 1935: solved affirmatively by Banach, also without
assuming continuity; see the commentary in R. D. Mauldin (ed.),
The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted doubly_ruled_graph_is_quadric :
    ∀ f : ℝ → ℝ → ℝ, DoublyRuledGraph f →
      ∃ a b c d e g : ℝ,
        (∀ x y : ℝ, f x y = a * x ^ 2 + b * x * y + c * y ^ 2 + d * x + e * y + g) ∧
        ((a = 0 ∧ b = 0 ∧ c = 0) ∨ b ^ 2 - 4 * a * c > 0)

end MathlibExt.Analysis.Calculus.ScottishBook44Wanted
