/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on split graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT;
H. Müller, "Hamiltonian circuits in chordal bipartite graphs", Discrete Mathematics 156 (1996),
291-298, doi:10.1016/0012-365X(95)00057-4 (NP-complete already for strongly chordal split graphs);
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 6 (1985), 434-451,
doi:10.1016/0196-6774(85)90012-4, Table 1 (split graphs: NP-complete, citing C. J. Colbourn and L. K. Stewart,
"Dominating cycles in series-parallel graphs", Ars Combinatoria 19A (1985), 107-112).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DominatingSetSplitGraphsWanted
public import WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitSplitGraphs

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-!
# HAMILTONIAN CIRCUIT on split graphs is NP-complete

INSTANCE: a split graph `G = (V, E)`, i.e. a graph whose vertex set can be partitioned into a
clique and an independent set.
QUESTION: does `G` contain a Hamiltonian circuit?

This is HAMILTONIAN CIRCUIT ([GT37]) restricted to split graphs. Müller (1996, abstract) proves
HAMILTONIAN CIRCUIT NP-complete for chordal bipartite graphs and, as a corollary, for strongly
chordal split graphs; every strongly chordal split graph is a split graph, so the problem is
NP-complete on split graphs. Johnson's Table 1 records the split-graph entry as NP-complete,
citing Colbourn and Stewart (1985), which was not available.

The instance, its well-formedness and the question are those of
`WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted` ([GT37]: a simple graph on
`Fin n` given by an edge list; a Hamiltonian circuit needs at least three vertices), as in
`ChordalBipartiteHamiltonianCircuitWanted`. The restriction adds the split-graph predicate
`DominatingSetSplitGraphs.IsSplitGraph` of `DominatingSetSplitGraphsWanted` (a vertex set that is
a clique, Mathlib's `SimpleGraph.IsClique`, whose complement is independent,
`SimpleGraph.IsIndepSet`; either part may be empty), as in `StronglyChordalSplitHamiltonianPathWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance whose graph is a
split graph. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ DominatingSetSplitGraphs.IsSplitGraph (Graph i)

open Classical in
/-- HAMILTONIAN CIRCUIT on split graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitSplitGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT on split graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT37]; Müller (1996); Johnson (1985), Table 1. -/
public theorem_wanted hamiltonianCircuitSplitGraphs_npComplete :
    hamiltonianCircuitSplitGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitSplitGraphsDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitSplitGraphs
