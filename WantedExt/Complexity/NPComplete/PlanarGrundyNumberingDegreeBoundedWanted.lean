/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH GRUNDY NUMBERING for planar digraphs with degree bounds is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT56];
A. S. Fraenkel, "Planar kernel and Grundy with d ≤ 3, dout ≤ 2, din ≤ 2 are NP-complete",
Discrete Applied Mathematics 3 (1981), 257-262, doi:10.1016/0166-218X(81)90003-2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PlanarGrundyNumberingDegreeBoundedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarGrundyNumberingDegreeBounded

/-!
# GRAPH GRUNDY NUMBERING for planar digraphs with degree bounds is NP-complete

INSTANCE: a directed graph `G = (V, A)` whose underlying graph is planar and in which every
vertex has total degree at most `3`, in-degree at most `2` and out-degree at most `2`.
QUESTION: does `G` have a Grundy numbering, i.e., a function `f : V → ℤ₀⁺` such that, for each
`v ∈ V`, `f(v)` is the least nonnegative integer not contained in the set
`{f(u) : u ∈ V, (v, u) ∈ A}`?

This is the restriction of GRAPH GRUNDY NUMBERING ([GT56], `GraphGrundyNumberingWanted`) to
Fraenkel's class: planar digraphs with `d ≤ 3`, `d_out ≤ 2`, `d_in ≤ 2`. The instance type,
digraph and question are the parent's; `WellFormed` is the parent's plus the restriction.
Planarity is MathlibExt's `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing,
equivalent to planarity for finite simple graphs by Fáry's theorem, as in
`PlanarSubgraphWanted`) of the underlying undirected graph `SimpleGraph.fromRel
(GraphGrundyNumbering.Graph i).Adj`. The out-degree of `v` is the number of arcs `(v, u)`, the
in-degree the number of arcs `(u, v)`, and the total degree their sum.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH GRUNDY NUMBERING for planar digraphs with degree bounds is NP-complete.** Source:
Garey and Johnson (1979), [GT56]; Fraenkel (1981). -/
public theorem_wanted planarGrundyNumberingDegreeBounded_npComplete :
    planarGrundyNumberingDegreeBoundedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarGrundyNumberingDegreeBoundedDec

end MetaMathlibExt.Complexity.NPComplete.PlanarGrundyNumberingDegreeBounded
