/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on star convex graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT (the parent
problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_1151` (star
convex), problem Hamiltonian cycle: NP-complete (reference note 1655, P. Irzhavsky: reductions
from HAMILTONIAN PATH on bipartite graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HamiltonianCircuitStarConvexDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitStarConvex

open HamiltonianCycleUndirected (HamiltonianCycleUndirectedInstance Graph
  HamiltonianCycleUndirectedFeasible)
open FeedbackVertexSetStarConvex (IsStarConvex)

/-!
# HAMILTONIAN CIRCUIT on star convex graphs is NP-complete

INSTANCE: a star convex bipartite graph `G = (V, E)`. QUESTION: does `G` contain a Hamiltonian
circuit?

This is HAMILTONIAN CIRCUIT ([GT37], stated on `main` as
`CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs`) on the ISGCI class
`gc_1151`: a bipartite graph `B = (X, Y, E)` is star convex if a tree `T = (X, F)` can be
defined such that `T` is a star and for every vertex `y ∈ Y` the neighbourhood of `y` induces a
subtree of `T`. The class predicate is `FeedbackVertexSetStarConvex.IsStarConvex` (from
`FeedbackVertexSetStarConvexWanted`, whose docstring explains the encoding), reused here.

ISGCI lists the problem as NP-complete with reference note 1655 (P. Irzhavsky), which reduces
HAMILTONIAN PATH on bipartite graphs `G = (X, Y, E)`: if `|X| < |Y|`, adding a vertex `x`
adjacent to all of `Y` gives a star convex graph (star on `X ∪ {x}` centred at `x`) with a
Hamiltonian cycle if and only if `G` has a Hamiltonian path; if `|X| = |Y|`, adding `x`, `u` to
`X` and `y`, `v` to `Y`, with `x` adjacent to `Y ∪ {y, v}`, `y` adjacent to `X ∪ {u}` and `u`
adjacent to `v`, gives a star convex graph (star centred at `x`) with a Hamiltonian cycle if and
only if `G` has a Hamiltonian path. A graph with one vertex has a Hamiltonian path, while the
first construction would give the 2-vertex graph `K₂`, which has no Hamiltonian circuit; that
instance is mapped to the fixed star convex yes-instance `C₄` instead. HAMILTONIAN PATH is
NP-complete on bipartite graphs (`HamiltonianPathBipartiteWanted`). Membership in NP holds for all
graphs, and the note shows that star convex graphs are recognized in linear time. A graph with an
isolated vertex and more than one vertex has no Hamiltonian circuit, so the binary vertex count does
not make the problem succinct.

The instance type, the graph, the parent's well-formedness (at least one vertex, simple edge list
on `Fin n`) and the question (`3 ≤ n` and Mathlib's `SimpleGraph.IsHamiltonian`) are the
parent's; the restriction adds star convexity to `WellFormed`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN CIRCUIT on star convex graphs is NP-complete.** Source: Garey and Johnson
(1979), [GT37]; ISGCI class `gc_1151` (reference note 1655). -/
public theorem_wanted hamiltonianCircuitStarConvex_npComplete :
    hamiltonianCircuitStarConvexDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitStarConvexDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitStarConvex
