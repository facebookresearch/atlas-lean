/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH GRUNDY NUMBERING for planar digraphs with in- and out-degrees at most 5 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT56] GRAPH GRUNDY NUMBERING,
comment: "Remains NP-complete when restricted to planar graphs in which no vertex has in- or
out-degree exceeding 5 [Fraenkel and Yesha, 1977]";
A. S. Fraenkel, "Planar kernel and Grundy with d ≤ 3, dout ≤ 2, din ≤ 2 are NP-complete",
Discrete Applied Mathematics 3 (1981), 257-262, doi:10.1016/0166-218X(81)90003-2 (a subclass).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PlanarGrundyNumberingDegreeFiveDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarGrundyNumberingDegreeFive

open GraphGrundyNumbering (GraphGrundyNumberingInstance GraphGrundyNumberingFeasible)
open PlanarGrundyNumberingDegreeBounded (inDegree outDegree)

/-!
# GRAPH GRUNDY NUMBERING for planar digraphs with in- and out-degrees at most 5 is NP-complete

INSTANCE: a directed graph `G = (V, A)` whose underlying graph is planar and in which no vertex
has in-degree or out-degree exceeding `5`.
QUESTION: does `G` have a Grundy numbering, i.e., a function `f : V → ℤ₀⁺` such that, for each
`v ∈ V`, `f(v)` is the least nonnegative integer not contained in the set
`{f(u) : u ∈ V, (v, u) ∈ A}`?

This is the restriction of GRAPH GRUNDY NUMBERING ([GT56], `GraphGrundyNumberingWanted`) printed
in Garey and Johnson's comment, with the attribution to Fraenkel and Yesha. Fraenkel (1981)
later proved the problem NP-complete for the smaller class of planar digraphs with total degree
at most `3` and in- and out-degree at most `2` (`PlanarGrundyNumberingDegreeBoundedWanted`);
those instances belong to this class, so hardness also follows from that published proof by a
reduction that keeps such instances and sends every other input to a fixed no-instance.

The instance type, the digraph and the question are the parent's; `WellFormed` is the parent's
plus the restriction, stated with the planarity predicate and the degree functions of
`PlanarGrundyNumberingDegreeBoundedWanted`: MathlibExt's `SimpleGraph.IsPlanar` of the
underlying undirected graph `SimpleGraph.fromRel (GraphGrundyNumbering.Graph i).Adj`, and
`PlanarGrundyNumberingDegreeBounded.inDegree`/`outDegree` (the numbers of arcs into and out of
`v`).

Membership in NP: the numbering (values at most `5`, since each vertex has at most `5`
out-neighbours) is a certificate, and planarity is checked in linear time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH GRUNDY NUMBERING for planar digraphs with in- and out-degrees at most `5` is
NP-complete.** Source: Garey and Johnson (1979), [GT56]; Fraenkel and Yesha (1977); Fraenkel
(1981). -/
public theorem_wanted planarGrundyNumberingDegreeFive_npComplete :
    planarGrundyNumberingDegreeFiveDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarGrundyNumberingDegreeFiveDec

end MetaMathlibExt.Complexity.NPComplete.PlanarGrundyNumberingDegreeFive
