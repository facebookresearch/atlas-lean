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

/-- **Line lying in a graph.** Let $f$ be a real-valued function of two real variables, and let
$x_0, y_0, u, v, w$ be real numbers. The line through $(x_0, y_0, f(x_0, y_0))$ with direction
$(u, v, w)$ lies in the graph of $f$ when $(u, v) \ne (0, 0)$ and
$f(x_0 + tu, y_0 + tv) = f(x_0, y_0) + tw$ for every real $t$. -/
def LineInGraph (f : ℝ → ℝ → ℝ) (x₀ y₀ u v w : ℝ) : Prop :=
  ¬ (u = 0 ∧ v = 0) ∧
    ∀ t : ℝ, f (x₀ + t * u) (y₀ + t * v) = f x₀ y₀ + t * w

/-- **Doubly ruled graph.** The graph of a real-valued function $f$ of two real variables is
doubly ruled when for every point $(x_0, y_0) \in \mathbb{R}^2$ there are $(u_1, v_1, w_1)$ and
$(u_2, v_2, w_2)$ in $\mathbb{R}^3$ such that the lines through $(x_0, y_0, f(x_0, y_0))$ with
directions $(u_1, v_1, w_1)$ and $(u_2, v_2, w_2)$ both lie in the graph of $f$, and $(u_2, v_2)$
is not a real multiple of $(u_1, v_1)$.

A line lying in the graph has a nonzero horizontal direction, so the last condition holds exactly
when the two lines are distinct. -/
def DoublyRuledGraph (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x₀ y₀ : ℝ, ∃ u₁ v₁ w₁ u₂ v₂ w₂ : ℝ,
    LineInGraph f x₀ y₀ u₁ v₁ w₁ ∧ LineInGraph f x₀ y₀ u₂ v₂ w₂ ∧
    ¬ ∃ c : ℝ, u₂ = c * u₁ ∧ v₂ = c * v₁

/--
**Doubly ruled graphs are planes or hyperbolic paraboloids.** Let $f$ be a real-valued
function of two real variables whose graph is doubly ruled; no continuity of $f$ is assumed. Then
there are real numbers $a, b, c, d, e, g$ such that
$f(x, y) = ax^2 + bxy + cy^2 + dx + ey + g$ for all real $x$ and $y$, and either $a = b = c = 0$
(the graph is a plane) or $b^2 - 4ac > 0$ (the graph is a hyperbolic paraboloid).

This answers Steinhaus's Problem 44 of the Scottish Book, which asks whether such a surface, the
graph of a continuous function, must be a hyperbolic paraboloid, and whether this can be proved
without continuity. Banach answered both questions affirmatively, with a proof based on the remark
that any two lines on the surface either intersect or have parallel projections on the
$xy$-plane; planes are the degenerate doubly ruled case.

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
