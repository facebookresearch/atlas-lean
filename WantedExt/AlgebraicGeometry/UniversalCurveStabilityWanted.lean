/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.UniversalCurveStability

@[expose] public section

/-!
# Determination of universal stability by small graphs

For genus at least two and at least one marking, the one-edge graphs and
the two-edge graphs with a rational component carrying a unique marking
determine the entire numerical stability parameter. Agreement is asserted
only on graphs of the actual prescribed genus and marking domain.

Source: Kass--Pagani, The stability space of compactified universal
Jacobians, Corollary 3.6. https://arxiv.org/abs/1707.02284
-/

namespace WantedExt.AlgebraicGeometry.UniversalCurveStability

open _root_.MathlibExt.AlgebraicGeometry.UniversalCurveStability

/-- **Two-vertex graphs determine universal stability parameters.** Kass–Pagani, Corollary 3.6,
for rational weights: let $g \ge 2$, $n \ge 1$ and $d \in \mathbb{Q}$, and let $\phi$, $\psi$ be
universal stability parameters of degree $d$ for connected stable $n$-marked graphs of genus $g$
(rational vertex weights summing to $d$ on each graph, invariant under graph isomorphisms, and such
that under a contraction each vertex weighs the sum of the weights of the vertices mapped to it).
If $\phi$ and $\psi$ agree on every graph with two vertices and no loops that has either one edge,
or two edges and a vertex of genus $0$ carrying exactly one marking, then they agree on every
connected stable $n$-marked graph of genus $g$. -/
public theorem_wanted stability_determined
    (g n : ℕ) (hg : 2 ≤ g) (hn : 1 ≤ n) (d : ℚ)
    (φ ψ : UniversalStability g n d)
    (agree : ∀ G : StableGraph g n, IsDeterminingGraph G →
      ∀ v, φ.weight G v = ψ.weight G v) :
    ∀ G : StableGraph g n, ∀ v, φ.weight G v = ψ.weight G v

end WantedExt.AlgebraicGeometry.UniversalCurveStability
