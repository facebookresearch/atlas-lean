/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on 3-connected cubic bipartite graphs is NP-complete

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
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitThreeConnectedCubicBipartite

open HamiltonianCycleUndirected (HamiltonianCycleUndirectedInstance Graph
  HamiltonianCycleUndirectedFeasible)

/-!
# HAMILTONIAN CIRCUIT on 3-connected cubic bipartite graphs is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` that is 3-connected, cubic (every vertex
has degree 3) and bipartite. QUESTION: does `G` contain a Hamiltonian circuit?

This is HAMILTONIAN CIRCUIT ([GT37], stated on `main` as
`WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted`) restricted to 3-connected cubic
bipartite graphs, which Akiyama, Nishizeki and Saito (1980) prove NP-complete. The instance type,
the graph, the parent's well-formedness (at least one vertex, simple edge list on `Fin n`) and the
question (`3 ≤ n` and Mathlib's `SimpleGraph.IsHamiltonian`) are the parent's; the restriction adds
to `WellFormed` that the graph is 3-connected, the shared MathlibExt predicate
`SimpleGraph.IsVertexConnected 3` (more than three vertices, and connected after deleting any set
of at most two vertices), cubic, Mathlib's `SimpleGraph.IsRegularOfDegree 3`, and bipartite,
Mathlib's `SimpleGraph.IsBipartite` (a proper 2-coloring). Membership in NP holds for all graphs,
and each restriction is decidable in polynomial time; a cubic graph has no isolated vertices, so
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

open Classical in
/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance (at least one
vertex, simple edge list on `Fin n`) whose graph is 3-connected, cubic and bipartite. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ (Graph i).IsVertexConnected 3 ∧
    (Graph i).IsRegularOfDegree 3 ∧ (Graph i).IsBipartite

open Classical in
/-- HAMILTONIAN CIRCUIT on 3-connected cubic bipartite graphs as a decision problem over
bitstrings. -/
noncomputable def hamiltonianCircuitThreeConnectedCubicBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT on 3-connected cubic bipartite graphs is NP-complete.** Source:
Akiyama, Nishizeki and Saito (1980); Garey and Johnson (1979), [GT37]. -/
public theorem_wanted hamiltonianCircuitThreeConnectedCubicBipartite_npComplete :
    hamiltonianCircuitThreeConnectedCubicBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitThreeConnectedCubicBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitThreeConnectedCubicBipartite
