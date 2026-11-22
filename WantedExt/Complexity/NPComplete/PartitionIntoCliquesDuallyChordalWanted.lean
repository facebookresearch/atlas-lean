/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES on dually chordal graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES (the
parent problem);
A. Brandstädt, F. F. Dragan, V. D. Chepoi and V. I. Voloshin, "Dually chordal graphs", SIAM
Journal on Discrete Mathematics 11(3) (1998), 437-455, doi:10.1137/S0895480193253415 (the
class);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_185` (dually
chordal), problem Clique cover: NP-complete (ISGCI reference note 1504: adding a universal
vertex to any graph gives a dually chordal graph with the same clique cover number).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.IndependentSetDuallyChordalWanted
public import WantedExt.Complexity.NPComplete.PartitionIntoCliquesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesDuallyChordal

open PartitionIntoCliques (PartitionIntoCliquesInstance Graph PartitionIntoCliquesFeasible)
open IndependentSetDuallyChordal (DuallyChordal)

/-!
# PARTITION INTO CLIQUES on dually chordal graphs is NP-complete

INSTANCE: a dually chordal graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: can `V` be partitioned into `k ≤ K` disjoint sets `V₁, …, V_k` such that each `Vᵢ`
induces a complete subgraph of `G`?

This is PARTITION INTO CLIQUES ([GT15], `PartitionIntoCliquesWanted`) on the ISGCI class
`gc_185`. ISGCI defines: a vertex `u` in the closed neighbourhood `N[v]` is a maximum neighbour
of `v` if `N[w] ⊆ N[u]` for all `w ∈ N[v]`; a vertex ordering `v₁ … vₙ` is a maximum
neighbourhood ordering if each `vᵢ` has a maximum neighbour in the subgraph `Gᵢ` induced by
`vᵢ, …, vₙ`; a graph is dually chordal if it has a maximum neighbourhood ordering. This is
`IndependentSetDuallyChordal.DuallyChordal` (from `IndependentSetDuallyChordalWanted`), reused
here.

ISGCI lists Clique cover as NP-complete on dually chordal graphs, with the reduction in its
reference note 1504: adding to a graph `G` a vertex `v` adjacent to all other vertices gives a
dually chordal graph (an ordering that puts `v` last is a maximum neighbourhood ordering, `v`
being a maximum neighbour of every vertex), and when `G` has a vertex, `G + v` has the same
clique cover number as `G` (`v` joins any clique of a partition of `G`, and deleting `v` from a
partition of `G + v` leaves a partition of `G` into at most as many cliques). Keeping `K` keeps
`0 < K ≤ |V|`, so this reduces PARTITION INTO CLIQUES to the restriction. Membership in NP: as
for the parent problem, a partition of the non-isolated vertices into cliques is a certificate
(every isolated vertex is a block of its own, so the binary vertex count does not make the
problem succinct), and an ordering of the non-isolated vertices, preceded by the isolated ones,
which are their own maximum neighbours, certifies the class.

The instance, the graph, the parent well-formedness condition (a simple edge list and
`0 < K ≤ |V|`) and the question are those of PARTITION INTO CLIQUES
(`PartitionIntoCliques.PartitionIntoCliquesInstance`, `PartitionIntoCliques.Graph`,
`PartitionIntoCliques.WellFormed`, `PartitionIntoCliques.PartitionIntoCliquesFeasible`: a block
map `c : V → Fin k` for some `k ≤ K` whose blocks are cliques; empty blocks are allowed and
harmless); this module adds the class to well-formedness.

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
list on the vertices `0, ..., n - 1` and `0 < K ≤ n`) whose graph is dually chordal. -/
def WellFormed (i : PartitionIntoCliquesInstance) : Prop :=
  PartitionIntoCliques.WellFormed i ∧ DuallyChordal (Graph i)

open Classical in
/-- PARTITION INTO CLIQUES on dually chordal graphs as a decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesDuallyChordalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoCliquesInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoCliquesFeasible i)
  | none => false

/-- **PARTITION INTO CLIQUES on dually chordal graphs is NP-complete.** Source: Garey and Johnson
(1979), [GT15]; ISGCI class `gc_185`, problem Clique cover (reference note 1504). -/
public theorem_wanted partitionIntoCliquesDuallyChordal_npComplete :
    partitionIntoCliquesDuallyChordalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoCliquesDuallyChordalDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesDuallyChordal
