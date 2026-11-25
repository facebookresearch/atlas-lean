/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES for K₃,₃-free graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES (the
unrestricted problem);
M. R. Cerioli, L. Faria, T. O. Ferreira, C. A. J. Martinhon, F. Protti and B. Reed, "Partition
into cliques for cubic graphs: Planar case, complexity and approximation", Discrete Applied
Mathematics 156(12) (2008), 2270-2278, doi:10.1016/j.dam.2007.10.015 (NP-complete for planar
cubic graphs);
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (row "K3,3-free", column PARTITION INTO CLIQUES);
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1 (row K3,3-FREE*, column CLI PAR: "N [77]").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PartitionIntoCliquesWanted
public import WantedExt.Complexity.NPComplete.DominatingSetK33FreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesK33Free

open MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliques
  (PartitionIntoCliquesInstance Graph PartitionIntoCliquesFeasible)
open MetaMathlibExt.Complexity.NPComplete.DominatingSetK33Free (HasK33Subdivision)

/-!
# PARTITION INTO CLIQUES for K₃,₃-free graphs is NP-complete

INSTANCE: a graph `G = (V, E)` with no subgraph homeomorphic to `K₃,₃`, and a positive integer
`K ≤ |V|`. QUESTION: can the vertices of `G` be partitioned into `k ≤ K` disjoint sets
`V₁, V₂, …, V_k` such that, for `1 ≤ i ≤ k`, the subgraph induced by `Vᵢ` is a complete graph?

This is the restriction of PARTITION INTO CLIQUES
(`WantedExt.Complexity.NPComplete.PartitionIntoCliquesWanted`, [GT15]) to the class that Johnson's
1985 table calls "K3,3-free" and de Figueiredo et al. call K3,3-FREE*: "the class of graphs that
contain no subgraphs homeomorphic to K3,3; in other words, the class of graphs that do not contain
K3,3 as a topological minor". The predicate is `DominatingSetK33Free.HasK33Subdivision` (a subgraph
homeomorphic to `K₃,₃`, i.e. a subdivision of `K₃,₃`: six distinct branch vertices joined by nine
paths that meet only at common endpoints). The instance, the graph, the parent well-formedness
condition (simple edge list, `0 < K ≤ |V|`) and the question are that module's; the restriction is
added to `WellFormed`. Every planar graph is K3,3-free (Kuratowski), so the class contains the
planar cubic graphs on which Cerioli et al. prove the problem NP-complete; de Figueiredo et al.
derive the K3,3-free entry from the planar one, citing Král', Kratochvíl, Tuza and Woeginger (WG
2001) for the planar case.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed PARTITION INTO CLIQUES instance (simple edge list,
`0 < K ≤ |V|`) whose graph has no subgraph homeomorphic to `K₃,₃`. -/
def WellFormed (i : PartitionIntoCliquesInstance) : Prop :=
  PartitionIntoCliques.WellFormed i ∧ ¬ HasK33Subdivision (Graph i)

open Classical in
/-- PARTITION INTO CLIQUES for K₃,₃-free graphs as a decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesK33FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoCliquesInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoCliquesFeasible i)
  | none => false

/-- **PARTITION INTO CLIQUES for K₃,₃-free graphs is NP-complete.** Source: Cerioli, Faria,
Ferreira, Martinhon, Protti and Reed (2008); Johnson (1985), Table 1; de Figueiredo, de Melo, Sasaki
and Silva (2022), Table 1. -/
public theorem_wanted partitionIntoCliquesK33Free_npComplete :
    partitionIntoCliquesK33FreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoCliquesK33FreeDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesK33Free
