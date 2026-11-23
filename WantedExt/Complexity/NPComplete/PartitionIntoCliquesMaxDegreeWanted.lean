/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES on graphs of maximum degree at most k (fixed k ≥ 3) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES, the
problem restricted here;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3)
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (degree-k graphs, PARTITION INTO
CLIQUES: NP-complete);
M. R. Cerioli, L. Faria, T. O. Ferreira, C. A. J. Martinhon, F. Protti and B. Reed,
"Partition into cliques for cubic graphs: Planar case, complexity and approximation", Discrete
Applied Mathematics 156(12) (2008), 2270-2278, doi:10.1016/j.dam.2007.10.015;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PartitionIntoCliquesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesMaxDegree

open PartitionIntoCliques (PartitionIntoCliquesInstance Graph PartitionIntoCliquesFeasible)

/-!
# PARTITION INTO CLIQUES on graphs of maximum degree at most k is NP-complete

Fix an integer `k ≥ 3`.
INSTANCE: a graph `G = (V, E)` in which no vertex has degree exceeding `k`, and a positive
integer `K ≤ |V|`.
QUESTION: can `V` be partitioned into `k' ≤ K` disjoint sets `V₁, …, V_k'` such that each `Vᵢ`
induces a complete subgraph of `G`?

This is PARTITION INTO CLIQUES ([GT15], `PartitionIntoCliquesWanted`) restricted to the
degree-`k` graphs of Johnson's Table 1 (1985), "graphs in which no vertex has degree exceeding
`k`", for a fixed `k`. Johnson lists the problem as NP-complete there; de Figueiredo, de Melo,
Sasaki and Silva (2022) note that the reduction cited for that entry does not bound degrees and
cite Cerioli, Faria, Ferreira, Martinhon, Protti and Reed (2008) instead, who prove PARTITION
INTO CLIQUES NP-complete for planar cubic graphs. A cubic graph has maximum degree `3 ≤ k`, so
their instances are instances of this problem for every fixed `k ≥ 3`, the range the theorem
below states. Membership in NP: the certificate is the partition.

The instance, the graph, the well-formedness `0 < K ≤ |V|` and the question are those of
`PartitionIntoCliquesWanted`; the restriction adds to the well-formedness that every vertex has
degree at most `k`, with Mathlib's `SimpleGraph.degree` on the instance graph.

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
/-- Well-formedness of an instance for the fixed degree bound `k`: well formed for PARTITION
INTO CLIQUES (a simple graph on `Fin n` and `0 < K ≤ n`), and no vertex has degree exceeding
`k`. -/
def WellFormed (k : ℕ) (i : PartitionIntoCliquesInstance) : Prop :=
  PartitionIntoCliques.WellFormed i ∧ ∀ v, (Graph i).degree v ≤ k

open Classical in
/-- PARTITION INTO CLIQUES on graphs of maximum degree at most `k`, for the fixed `k`, as a
decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesMaxDegreeDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoCliquesInstance) x with
  | some i => decide (WellFormed k i ∧ PartitionIntoCliquesFeasible i)
  | none => false

/-- **PARTITION INTO CLIQUES on graphs of maximum degree at most `k` is NP-complete for every
fixed `k ≥ 3`.** Source: Johnson (1985), Table 1; Cerioli, Faria, Ferreira, Martinhon, Protti and
Reed (2008); Garey and Johnson (1979), [GT15]. -/
public theorem_wanted partitionIntoCliquesMaxDegree_npComplete (k : ℕ) (_hk : 3 ≤ k) :
    partitionIntoCliquesMaxDegreeDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (partitionIntoCliquesMaxDegreeDec k)

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesMaxDegree
