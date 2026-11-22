/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Real roots of the flow polynomial (Open Problem Garden 135)

Open Problem Garden, Real roots of the flow polynomial (D. J. A. Welsh): all real roots of nonzero
flow polynomials are at most `4`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace MathlibExt.GraphTheory.FlowPolynomialRealRootsOpenGardenProblem135Wanted

/-!
Source: Open Problem Garden, Real roots of the flow polynomial (node 135; D. J. A. Welsh),
http://www.openproblemgarden.org/op/real_roots_of_the_flow_polynomial. UnsolvedMath record
UM-00003221 (`OPG-135`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs may have loops and parallel edges: a finite edge type `E` with an endpoint map `ends : E →
Sym2 V`. The flow polynomial is given by its subset expansion `Φ(G, x) = ∑_{A ⊆ E} (-1)^{|E \ A|}
x^{|A| + c(A) - |V|}`, `c(A)` the number of components of `(V, A)`; for a positive integer `k`,
`Φ(G, k)` is the number of nowhere-zero `ℤ/k`-flows (the expansion is the one used for Open Problem
Garden 348 in `OpenConjectures/GraphTheory/OpenGardenProblem348`). Nonzero means not identically
zero (a graph with a bridge has `Φ = 0`); a real root is a real `x` with `Φ(G, x) = 0`.
-/

variable {V E : Type}

/-- The spanning subgraph with edge set `A`, as a simple graph on `V` (loops and edge multiplicities
do not affect connectivity). -/
def spanning (ends : E → Sym2 V) (A : Finset E) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => ∃ e ∈ A, ends e = s(u, v)

/-- The flow polynomial of the graph `(V, E, ends)` (loops and parallel edges allowed) evaluated at
`x`, by its subset expansion `Φ(x) = ∑_{A ⊆ E} (-1)^{|E \ A|} x^{|A| + c(A) - |V|}`, where
`c(A)` is the number of connected components of `(V, A)`; for a positive integer `k`, `Φ(k)` is the
number of nowhere-zero `ℤ/k`-flows. -/
noncomputable def flowPolynomial [Fintype V] [Fintype E] (ends : E → Sym2 V) (x : ℝ) : ℝ :=
  ∑ A : Finset E, (-1 : ℝ) ^ (Fintype.card E - A.card) *
    x ^ (A.card + Nat.card (spanning ends A).ConnectedComponent - Fintype.card V)

/-- Welsh's conjecture: every real root of a flow polynomial that is not identically zero is at
most `4`. -/
def flowRootsAtMostFour : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (ends : E → Sym2 V),
    (∃ x : ℝ, flowPolynomial ends x ≠ 0) → ∀ x : ℝ, flowPolynomial ends x = 0 → x ≤ 4

/--
Resolved false: Haggard, Pearce and Royle found graphs with real flow roots in `(4, ∞)`, and
Jacobsen and Salas compute the flow polynomial of the generalised Petersen graph `G(119,7)` (cubic
and bridgeless, so its flow polynomial is not identically zero), which has real roots near
`5.0000197675` and `5.1653424423`. The witness is one explicit graph with `357` edges, far beyond a
direct evaluation of the subset expansion. Source: Open Problem Garden, Real roots of the flow
polynomial (node 135; D. J. A. Welsh),
http://www.openproblemgarden.org/op/real_roots_of_the_flow_polynomial; resolution: J. L. Jacobsen
and J. Salas, Is the five-flow conjecture almost false?, J. Combin. Theory Ser. B 103 (2013),
532-565; arXiv:1009.4062, abstract: Welsh's conjecture that the flow polynomial has no real roots in
(4, ∞) was disproved by Haggard, Pearce and Royle; the flow polynomial of the generalised Petersen
graph G(119,7) has real roots Q ≈ 5.0000197675 and Q ≈ 5.1653424423. The Open Problem Garden page
records the disproof in comments by G. Royle and R. Šámal,
https://doi.org/10.1016/j.jctb.2013.06.001.
-/
public theorem_wanted flowRootsAtMostFour_refuted : ¬ flowRootsAtMostFour

end MathlibExt.GraphTheory.FlowPolynomialRealRootsOpenGardenProblem135Wanted
