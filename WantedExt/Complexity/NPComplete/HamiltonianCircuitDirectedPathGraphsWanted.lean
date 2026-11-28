/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT ON DIRECTED PATH GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT, the problem
restricted here;
G. Narasimhan, "A note on the Hamiltonian circuit problem on directed path graphs", Information
Processing Letters 32 (1989), 167-170, doi:10.1016/0020-0190(89)90038-0;
C. L. Monma and V. K. Wei, "Intersection graphs of paths in a tree", Journal of Combinatorial
Theory, Series B 41 (1986), 141-181, doi:10.1016/0095-8956(86)90042-1 (the class).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HamiltonianCircuitDirectedPathGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitDirectedPathGraphs

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance Graph HamiltonianCycleUndirectedFeasible)

/-!
# HAMILTONIAN CIRCUIT ON DIRECTED PATH GRAPHS is NP-complete

INSTANCE: a directed path graph `G = (V, E)`: the vertex intersection graph of a family of directed
paths in a tree with oriented edges (ISGCI class `gc_175`; the tree may or may not have a root, i.e.
its orientation is arbitrary).
QUESTION: does `G` contain a Hamiltonian circuit, i.e. a simple cycle through every vertex?

Narasimhan proves HAMILTONIAN CIRCUIT (and HAMILTONIAN PATH) NP-complete on directed path graphs,
the class of Monma and Wei (their `DV`), answering the question left open by Bertossi and
Bonuccelli's result for undirected path graphs. Membership in NP is immediate (the circuit is a
certificate).

The instance, the graph and the question are those of HAMILTONIAN CIRCUIT
(`HamiltonianCycleUndirectedDefs`), reused unchanged: a vertex count `n` and an edge list on
`Fin n` (`HamiltonianCycleUndirected.HamiltonianCycleUndirectedInstance`,
`HamiltonianCycleUndirected.Graph`), the parent's well-formedness
(`HamiltonianCycleUndirected.WellFormed`: `0 < n` and a simple edge list), and the question
`HamiltonianCycleUndirected.HamiltonianCycleUndirectedFeasible` (`3 ≤ n` and Mathlib's
`SimpleGraph.IsHamiltonian`: a cycle through every vertex). The restriction adds that the graph is a
directed path graph (`IsDirectedPathGraph`): there are a finite tree `T` (Mathlib's
`SimpleGraph.IsTree`) on `Fin m`, an orientation `D` of its edges (MathlibExt's
`SimpleGraph.IsOrientation`: `D` relates only adjacent vertices and orients every edge `xy` of `T`
exactly one way, `D x y` or `D y x`), and for every vertex `v` of `G` the vertex set `P v` of a path
of `T` all of whose edges are traversed along their orientation, such that two distinct vertices are
adjacent in `G` exactly when their paths share a vertex of `T`. This follows
`DominatingSetUndirectedPathGraphsWanted.IsUndirectedPathGraph`, adding the orientation; a path may
consist of a single tree vertex.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN CIRCUIT ON DIRECTED PATH GRAPHS is NP-complete.** Source: Garey and Johnson
(1979), [GT37]; Narasimhan (1989). -/
public theorem_wanted hamiltonianCircuitDirectedPathGraphs_npComplete :
    hamiltonianCircuitDirectedPathGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitDirectedPathGraphsDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitDirectedPathGraphs
