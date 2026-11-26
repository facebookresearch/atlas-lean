/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on comparability graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT, comment
("Remains NP-complete [...] (2) if G is bipartite [Krishnamoorthy, 1975]");
M. S. Krishnamoorthy, "An NP-hard problem in bipartite graphs", ACM SIGACT News 7(1) (1975), 26,
doi:10.1145/990518.990521;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3)
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (comparability graphs, HAMILTONIAN
CIRCUIT: NP-complete, citing T. Akiyama, T. Nishizeki and N. Saito, "NP-completeness of the
Hamiltonian cycle problem for bipartite graphs", Journal of Information Processing 3 (1980),
73-76);
H. Müller, "Hamiltonian circuits in chordal bipartite graphs", Discrete Mathematics 156 (1996),
291-298, doi:10.1016/0012-365X(95)00057-4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ComparabilityGraphSandwichWanted
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitComparability

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-!
# HAMILTONIAN CIRCUIT on comparability graphs is NP-complete

INSTANCE: a comparability graph `G = (V, E)`.
QUESTION: does `G` contain a Hamiltonian circuit?

The instance, its well-formedness and the question are those of
`CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs` ([GT37]: a simple graph on
`Fin n` given by an edge list; a Hamiltonian circuit needs at least three vertices). The
restriction adds that the graph is a comparability graph.

A comparability graph (a transitively orientable graph) is the comparability graph of a partial
order: `ComparabilityGraphSandwich.IsComparabilityGraph` from
`WantedExt.Complexity.NPComplete.ComparabilityGraphSandwichWanted` (some strict partial order `r`
on the vertices, Mathlib's `IsStrictOrder`, makes two vertices adjacent exactly when they are
comparable under `r`), as in `FeedbackVertexSetComparabilityWanted`.

Garey and Johnson record that HAMILTONIAN CIRCUIT remains NP-complete for bipartite graphs
(Krishnamoorthy 1975), Johnson's Table 1 (1985) lists it as NP-complete for comparability
graphs (citing Akiyama, Nishizeki and Saito 1980, bipartite graphs), and Müller (1996) proves it
NP-complete for chordal bipartite graphs. Every bipartite graph is a comparability graph:
ordering each vertex of one side below its neighbors on the other side is a strict partial order
(there are no chains of length 2, so transitivity holds vacuously) whose comparable pairs are
exactly the edges. Membership in NP: the certificate is a Hamiltonian circuit together with a
transitive orientation of `G`, both checkable in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance (a simple edge
list on `Fin n`, `n > 0`) whose graph is a comparability graph. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧
    ComparabilityGraphSandwich.IsComparabilityGraph (Graph i)

open Classical in
/-- HAMILTONIAN CIRCUIT on comparability graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitComparabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT on comparability graphs is NP-complete.** Source: Garey and Johnson
(1979), [GT37], comment; Krishnamoorthy (1975); Johnson (1985), Table 1. -/
public theorem_wanted hamiltonianCircuitComparability_npComplete :
    hamiltonianCircuitComparabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitComparabilityDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitComparability
