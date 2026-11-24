/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT for bipartite graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT, comment (2);
M. S. Krishnamoorthy, "An NP-hard problem in bipartite graphs", ACM SIGACT News 7(1) (1975), 26,
doi:10.1145/990518.990521;
T. Akiyama, T. Nishizeki and N. Saito, "NP-completeness of the Hamiltonian cycle problem for
bipartite graphs", Journal of Information Processing 3 (1980), 73-76.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitBipartite

open HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance Graph HamiltonianCycleUndirectedFeasible)

/-!
# HAMILTONIAN CIRCUIT for bipartite graphs is NP-complete

INSTANCE: a bipartite graph `G = (V, E)`.
QUESTION: does `G` contain a Hamiltonian circuit?

Garey and Johnson record in the comments to [GT37] that HAMILTONIAN CIRCUIT remains NP-complete
"(2) if `G` is bipartite [Krishnamoorthy, 1975]". Krishnamoorthy shows that checking for a
Hamiltonian circuit in bipartite graphs is NP-hard; Akiyama, Nishizeki and Saito prove the
stronger result for planar bipartite graphs of maximum degree 3
(`HamiltonianCircuitPlanarBipartiteSubcubicWanted`). A Hamiltonian circuit is a polynomial
certificate, and bipartiteness is decidable in polynomial time (breadth-first 2-colouring), so
the problem is in NP. A Hamiltonian circuit uses `|V|` edges, so an instance with more vertices
than listed edges is a no-instance and the binary vertex count does not make the problem
succinct.

The instance, the graph, the parent well-formedness (at least one vertex and a simple edge list)
and the question are those of HAMILTONIAN CIRCUIT
(`HamiltonianCycleUndirected.HamiltonianCycleUndirectedInstance`,
`HamiltonianCycleUndirected.Graph`, `HamiltonianCycleUndirected.WellFormed`,
`HamiltonianCycleUndirected.HamiltonianCycleUndirectedFeasible`: at least three vertices and
Mathlib's `SimpleGraph.IsHamiltonian`), reused unchanged. The restriction adds to `WellFormed`
that the graph is bipartite: Mathlib's `SimpleGraph.IsBipartite` (`Colorable 2`), as in
`HamiltonianPathBipartiteWanted` and `FeedbackVertexSetBipartiteWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance (at least one
vertex and a simple edge list on the vertices `0, ..., n - 1`) whose graph is bipartite
(`SimpleGraph.IsBipartite`). -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ (Graph i).IsBipartite

open Classical in
/-- HAMILTONIAN CIRCUIT for bipartite graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT for bipartite graphs is NP-complete.** Source: Garey and Johnson
(1979), [GT37]; Krishnamoorthy (1975); Akiyama, Nishizeki and Saito (1980). -/
public theorem_wanted hamiltonianCircuitBipartite_npComplete :
    hamiltonianCircuitBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitBipartite
