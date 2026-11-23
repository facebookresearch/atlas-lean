/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES on locally connected graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES (the
parent problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_932` (locally
connected), problem Clique cover: NP-complete, reference `ref_1506` (ISGCI note: adding a
universal vertex to a connected graph yields a locally connected graph with the same clique
cover number; communicated by P. Irzhavski). No published proof was found.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PartitionIntoCliquesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesLocallyConnected

open PartitionIntoCliques (PartitionIntoCliquesInstance Graph PartitionIntoCliquesFeasible)

/-!
# PARTITION INTO CLIQUES on locally connected graphs is NP-complete

INSTANCE: a locally connected graph `G = (V, E)`, and a positive integer `K ≤ |V|`.
QUESTION: can the vertices of `G` be partitioned into `k ≤ K` disjoint sets `V₁, ..., Vₖ` such
that, for `1 ≤ i ≤ k`, the subgraph induced by `Vᵢ` is a complete graph?

This is PARTITION INTO CLIQUES ([GT15], ISGCI's "Clique cover") on the ISGCI class `gc_932`.
ISGCI's definition: "A graph G is locally connected iff for every vertex v, the open
neighbourhood N(v) of v induces a connected graph in G." Here that is
`∀ v, (G.induce (G.neighborSet v)).Connected`, as in `LocallyConnectedHamiltonianCircuitWanted`.
Mathlib's `SimpleGraph.Connected` includes nonemptiness, so a graph with an isolated vertex is
not locally connected here; the definition does not say whether an empty neighbourhood induces a
connected graph, and the reduction below produces no isolated vertex, so hardness holds under
either reading.

The instance, the graph, the parent well-formedness (`PartitionIntoCliques.WellFormed`: a simple
edge list on `Fin n` and `0 < K ≤ |V|`) and the question
(`PartitionIntoCliques.PartitionIntoCliquesFeasible`) are those of `PartitionIntoCliquesWanted`,
unchanged; the restriction adds to `WellFormed` that the graph is locally connected.

Reduction from PARTITION INTO CLIQUES on connected graphs (ISGCI note `ref_1506`): for a
connected graph `G` with at least one vertex, adding a vertex `u` adjacent to all others gives a
locally connected graph (`N(u)` induces `G`, and every other `N(v)` contains `u`, which is
adjacent to the rest of `N(v)`) with the same clique cover number (`u` joins any clique of a
cover of `G`, and deleting `u` from a cover of the new graph leaves a cover of `G` with no more
cliques). The partition is a polynomial certificate and local connectivity is checkable in
polynomial time, so the problem is in NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed PARTITION INTO CLIQUES instance (a simple edge
list on `Fin n`, `0 < K ≤ |V|`) whose graph is locally connected (the neighbourhood of every
vertex induces a connected graph). -/
def WellFormed (i : PartitionIntoCliquesInstance) : Prop :=
  PartitionIntoCliques.WellFormed i ∧
    ∀ v, ((Graph i).induce ((Graph i).neighborSet v)).Connected

open Classical in
/-- PARTITION INTO CLIQUES on locally connected graphs as a decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesLocallyConnectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoCliquesInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoCliquesFeasible i)
  | none => false

/-- **PARTITION INTO CLIQUES on locally connected graphs is NP-complete.** Source: ISGCI
(`gc_932`, note `ref_1506`); Garey and Johnson (1979), [GT15] (parent problem). -/
public theorem_wanted partitionIntoCliquesLocallyConnected_npComplete :
    partitionIntoCliquesLocallyConnectedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoCliquesLocallyConnectedDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesLocallyConnected
