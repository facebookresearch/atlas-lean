/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY ON B₀-VPG GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC
NUMBER), the problem restricted here;
A. Asinowski, E. Cohen, M. C. Golumbic, V. Limouzy, M. Lipshteyn, and M. Stern, "Vertex
intersection graphs of paths on a grid", Journal of Graph Algorithms and Applications 16 (2012),
129-150, doi:10.7155/jgaa.00253, Theorem 8.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GraphColoringBZeroVPGDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoringBZeroVPG

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# GRAPH K-COLORABILITY ON B₀-VPG GRAPHS is NP-complete

INSTANCE: a `B₀`-VPG graph `G = (V, E)` and a positive integer `m` with `3 ≤ m ≤ |V|`.
QUESTION: is `χ(G) ≤ m`, i.e. is there a map `c : V → {1, …, m}` with `c(u) ≠ c(v)` for every
edge `uv`?

Asinowski, Cohen, Golumbic, Limouzy, Lipshteyn, and Stern, Theorem 8: "Let G be a B₀-VPG graph
and let m be a positive integer (m ≥ 3). It is NP-complete to decide if χ(G) ≤ m." A graph is
`B₀`-VPG if it is the vertex intersection graph of a set of simple paths with no bend on a
rectangular grid: each vertex `v` is a horizontal or vertical grid segment `P_v`, and distinct
`u, v` are adjacent exactly when `P_u` and `P_v` share a grid point (ISGCI class `gc_1065`).
Membership in NP is immediate (a representation and a coloring are a certificate).

The instance, the graph and the question are those of `GraphColoringWanted`, reused unchanged:
vertex count, edge list on `Fin n` and number of colors `K`, with `GraphColoring.WellFormed`,
`GraphColoring.Graph` and `GraphColoring.GraphColoringFeasible` (`(Graph i).Colorable i.2.2`). The
restriction adds `3 ≤ m`, `m ≤ |V|` (the bound of Garey and Johnson's [GT4]; a larger `m` makes the
question trivially yes), and a `B₀`-VPG representation. The grid points are `ℕ × ℕ` (a finite
rectangular grid can be translated into it), and the segment of `v` is the set of grid points
`Set.Icc (lo v) (hi v)` for the componentwise order, with `lo v ≤ hi v` and `lo v`, `hi v` on a
common horizontal or vertical grid line; a segment with `lo v = hi v` is a single grid point (a path
with no edge). This mirrors the rectangle representation of `BoxicityTwoWanted` (`Set.Icc` in
`ℝ × ℝ`) with grid points and segments in place of real rectangles.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH K-COLORABILITY ON B₀-VPG GRAPHS is NP-complete.** Source: Garey and Johnson (1979),
[GT4]; Asinowski, Cohen, Golumbic, Limouzy, Lipshteyn, and Stern (2012), Theorem 8. -/
public theorem_wanted graphColoringBZeroVPG_npComplete :
    graphColoringBZeroVPGDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphColoringBZeroVPGDec

end MetaMathlibExt.Complexity.NPComplete.GraphColoringBZeroVPG
