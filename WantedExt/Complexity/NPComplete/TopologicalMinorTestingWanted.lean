/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOPOLOGICAL MINOR TESTING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), open problem [OPEN2] SUBGRAPH HOMEOMORPHISM
(FOR A FIXED GRAPH H), p. 285, comment: "If H is allowed to vary as part of the instance, the
problem is NP-complete, since it contains HAMILTONIAN CIRCUIT as a special case";
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9
(HAMILTONIAN CIRCUIT, Garey and Johnson's [GT37]).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TopologicalMinorTestingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TopologicalMinorTesting

/-!
# TOPOLOGICAL MINOR TESTING is NP-complete

INSTANCE: graphs `G = (V, E)` and `H = (V_H, E_H)`.
QUESTION: does `G` contain a subdivision of `H` as a subgraph, i.e., does `G` contain a subgraph
homeomorphic to `H`?

Garey and Johnson ([OPEN2]) define the question for a fixed `H` as: does `G` contain a subgraph
`G' = (V', E')` that can be converted to a graph isomorphic to `H` by repeatedly removing any
vertex of degree 2 and adding the edge joining its two neighbors? For fixed `H` its complexity
is listed as open; their comment records that the problem is NP-complete when `H` is part of the
instance, the version stated here. For a graph `G` with `n ≥ 3` vertices and `H` the cycle on
`n` vertices, a subdivision of `H` inside `G` has at least `n` vertices, hence no subdivision
vertices, so it is a Hamiltonian circuit of `G`, and conversely a Hamiltonian circuit is such a
subgraph; this is the special case HAMILTONIAN CIRCUIT ([GT37], Karp 1972).

A subdivision of `H` in `G` is stated directly: a one-to-one map `φ : V_H → V` (the branch
vertices) and, for each edge `{a, b}` of `H`, a path in `G` from `φ a` to `φ b`, such that no
path passes through a branch vertex other than its two ends, and paths of different edges share
no vertex other than branch vertices (they are internally vertex-disjoint). This is equivalent
to Garey and Johnson's formulation. Suppressing the inner vertices of the paths turns such a
subgraph into `H`. Conversely, a step "remove a vertex of degree 2 and add the edge joining its
two neighbors" undoes the subdivision of an edge when the two neighbors are not adjacent; when
they are adjacent, it deletes a vertex if graphs stay simple, and creates a parallel edge that
no later step removes if they are read as multigraphs (so it never occurs on the way to the
simple graph `H`). Undoing a subdivision and deleting a vertex both preserve containing a
subdivision of the result.

The vertices of `G` are `0, …, n - 1` and those of `H` are `0, …, m - 1`; both graphs are given
by simple edge lists (no loops, no repeated edge in either orientation, endpoints in range), so
the entries of `H`'s list are its edges, one each. Paths are Mathlib walks `p : G.Walk u v` with
`p.IsPath`, as in `DisjointConnectingPathsWanted`; path `j` realizes the `j`-th edge of `H`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TOPOLOGICAL MINOR TESTING is NP-complete.** Source: Garey and Johnson (1979), [OPEN2]
comment, [GT37]; Karp (1972). -/
public theorem_wanted topologicalMinorTesting_npComplete :
    topologicalMinorTestingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L topologicalMinorTestingDec

end MetaMathlibExt.Complexity.NPComplete.TopologicalMinorTesting
