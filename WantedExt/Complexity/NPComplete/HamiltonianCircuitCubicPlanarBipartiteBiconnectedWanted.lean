/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on 2-connected cubic planar bipartite graphs is NP-complete

Source:
T. Akiyama, T. Nishizeki and N. Saito, "NP-completeness of the Hamiltonian cycle problem for
bipartite graphs", Journal of Information Processing 3(2) (1980), 73-76 (abstract: "We show that
this problem is NP-complete for two classes of bipartite graphs: 2-connected cubic bipartite
planar graphs; and 3-connected cubic bipartite graphs.");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT (the parent
problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HamiltonianCircuitCubicPlanarBipartiteBiconnectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitCubicPlanarBipartiteBiconnected

open HamiltonianCycleUndirected (HamiltonianCycleUndirectedInstance Graph
  HamiltonianCycleUndirectedFeasible)

/-!
# HAMILTONIAN CIRCUIT on 2-connected cubic planar bipartite graphs is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` that is 2-connected, cubic (every vertex
has degree 3), planar and bipartite. QUESTION: does `G` contain a Hamiltonian circuit?

This is HAMILTONIAN CIRCUIT ([GT37]) restricted to 2-connected cubic bipartite planar graphs,
which Akiyama, Nishizeki and Saito (1980) prove NP-complete. It is the problem of
`HamiltonianCircuitCubicPlanarBiconnectedWanted` (2-connected cubic planar graphs) with the
further restriction that the graph is bipartite: the instance type, the graph, that module's
`WellFormed` (a well-formed HAMILTONIAN CIRCUIT instance whose graph is 2-connected, the shared
MathlibExt predicate `SimpleGraph.IsVertexConnected 2`, cubic, Mathlib's
`SimpleGraph.IsRegularOfDegree 3`, and planar, the shared MathlibExt predicate
`SimpleGraph.IsPlanar`) and the question (`3 ≤ n` and Mathlib's `SimpleGraph.IsHamiltonian`) are
reused unchanged, and `WellFormed` adds Mathlib's `SimpleGraph.IsBipartite` (a proper
2-coloring). Membership in NP holds for all graphs; a cubic graph has no isolated vertices, so
`n ≤ 2|E|` and the binary vertex count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN CIRCUIT is NP-complete on 2-connected cubic planar bipartite graphs.** Source:
Akiyama, Nishizeki and Saito (1980); Garey and Johnson (1979), [GT37]. -/
public theorem_wanted hamiltonianCircuitCubicPlanarBipartiteBiconnected_npComplete :
    hamiltonianCircuitCubicPlanarBipartiteBiconnectedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitCubicPlanarBipartiteBiconnectedDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitCubicPlanarBipartiteBiconnected
