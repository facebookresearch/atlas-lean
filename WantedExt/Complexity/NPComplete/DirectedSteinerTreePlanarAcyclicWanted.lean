/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED STEINER TREE in planar acyclic graphs with equal weights is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 5 (1984), 147-160,
doi:10.1016/0196-6774(84)90045-2, Section 1, STEINER TREE IN GRAPHS [ND12]: the directed version
"is NP-complete even for acyclic planar graphs with all edge weights equal", credited to
J. S. Provan, "A polynomial algorithm for the Steiner tree problem on terminal-planar graphs",
Report No. UNC/ORSA/TR-83/10, University of North Carolina, Chapel Hill (1983) (not available);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DirectedSteinerTreePlanarAcyclicDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedSteinerTreePlanarAcyclic

/-!
# DIRECTED STEINER TREE in planar acyclic graphs with equal weights is NP-complete

INSTANCE: an acyclic directed graph `G = (V, A)` that is planar, with all arc weights equal
(taken to be `1`), a source vertex `s ∈ V`, a set `T ⊆ V` of sink vertices, and a positive
integer bound `B`.
QUESTION: is there a subgraph of `G` with at most `B` arcs (weight at most `B`) that contains a
directed path from `s` to `t` for every `t ∈ T`?

This is the directed version of STEINER TREE IN GRAPHS [ND12] in Johnson's column, restricted to
acyclic planar graphs with all edge weights equal. "Source" and "sink" are Johnson's names for
the start and the ends of the required paths ("a specified source vertex `s`, and a set `T` of
sink vertices"); no in- or out-degree condition is imposed on them. With every weight equal to
`w > 0`, a subgraph has weight at most `w · B` exactly when it has at most `B` arcs, so the
weights are dropped and the subgraph's weight is its number of arcs. The positive bound is
[ND12]'s convention.

The digraph has vertices `0, …, n - 1` and is given by its list of distinct arcs (`(u, v)` is the
arc `u → v`). Acyclic means that no vertex reaches itself along one or more arcs
(`Relation.TransGen`). A digraph is planar when its underlying undirected graph is, so planarity
is the shared MathlibExt predicate `SimpleGraph.IsPlanar` applied to
`Cslib.Complexity.Karp.edgeGraph n A`, which joins `u` and `v` when either arc is present. A
subgraph is given by its arcs, a sublist of `A`; its vertices play no role in the question. A
directed path from `s` to `t` in it exists exactly when `t` is reachable from `s` along its arcs
(`Relation.ReflTransGen`; the empty path when `t = s`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DIRECTED STEINER TREE in planar acyclic graphs with equal weights is NP-complete.**
Source: Johnson (1984), STEINER TREE IN GRAPHS [ND12] (Provan, 1983). -/
public theorem_wanted directedSteinerTreePlanarAcyclic_npComplete :
    directedSteinerTreePlanarAcyclicDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedSteinerTreePlanarAcyclicDec

end MetaMathlibExt.Complexity.NPComplete.DirectedSteinerTreePlanarAcyclic
