/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT IN UNDIRECTED PATH GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT;
A. A. Bertossi and M. A. Bonuccelli, "Hamiltonian circuits in interval graph generalizations",
Information Processing Letters 23 (1986), 195-200, doi:10.1016/0020-0190(86)90135-3;
ISGCI (Information System on Graph Classes and their Inclusions), class undirected path (gc_129),
problem Hamiltonian cycle: NP-complete [Bertossi and Bonuccelli 1986].
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DominatingSetUndirectedPathGraphsWanted
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UndirectedPathGraphHamiltonianCircuit

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance Graph HamiltonianCycleUndirectedFeasible)

/-!
# HAMILTONIAN CIRCUIT IN UNDIRECTED PATH GRAPHS is NP-complete

INSTANCE: an undirected path graph `G = (V, E)`, that is, the vertex intersection graph of a
family of paths in an undirected tree.
QUESTION: does `G` have a Hamiltonian circuit, that is, a simple cycle through every vertex?

This is HAMILTONIAN CIRCUIT (`HamiltonianCycleUndirectedDefs`, Garey and Johnson [GT37])
restricted to undirected path graphs. Bertossi and Bonuccelli show that finding a Hamiltonian
circuit is NP-complete for undirected path graphs (and hence chordal graphs), double interval
graphs and rectangle graphs.

The instance, the graph and the question are those of `HamiltonianCycleUndirectedDefs`, reused
unchanged: vertex count and edge list on `Fin n`, with `HamiltonianCycleUndirected.WellFormed`
(at least one vertex, simple edge list), `HamiltonianCycleUndirected.Graph` and
`HamiltonianCycleUndirectedFeasible` (at least three vertices and Mathlib's
`SimpleGraph.IsHamiltonian`). The restriction adds to well-formedness that the graph is an
undirected path graph, with the definition already in the repository,
`DominatingSetUndirectedPathGraphs.IsUndirectedPathGraph`: for some finite tree `T` (Mathlib's
`SimpleGraph.IsTree`) each vertex `v` has the vertex set `P v` of a path in `T` (a
`SimpleGraph.Walk` with `IsPath`), and distinct vertices are adjacent exactly when their paths
share a vertex of `T`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance whose graph is an
undirected path graph. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧
    DominatingSetUndirectedPathGraphs.IsUndirectedPathGraph (Graph i)

open Classical in
/-- HAMILTONIAN CIRCUIT IN UNDIRECTED PATH GRAPHS as a decision problem over bitstrings. -/
noncomputable def undirectedPathGraphHamiltonianCircuitDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT IN UNDIRECTED PATH GRAPHS is NP-complete.**
Source: Garey and Johnson (1979), [GT37];
Bertossi and Bonuccelli (1986). -/
public theorem_wanted undirectedPathGraphHamiltonianCircuit_npComplete :
    undirectedPathGraphHamiltonianCircuitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L undirectedPathGraphHamiltonianCircuitDec

end MetaMathlibExt.Complexity.NPComplete.UndirectedPathGraphHamiltonianCircuit
