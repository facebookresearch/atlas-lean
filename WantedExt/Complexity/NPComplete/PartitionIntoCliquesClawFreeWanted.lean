/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES for claw-free graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES;
F. Maffray and M. Preissmann, "On the NP-completeness of the k-colorability problem for
triangle-free graphs", Discrete Mathematics 162 (1996), 313-317,
doi:10.1016/S0012-365X(97)89267-9;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1 and Section 2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Combinatorics.SimpleGraph.ClawFreeIndependencePoly
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PartitionIntoCliquesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesClawFree

open PartitionIntoCliques (PartitionIntoCliquesInstance Graph PartitionIntoCliquesFeasible)

/-!
# PARTITION INTO CLIQUES for claw-free graphs is NP-complete

INSTANCE: a claw-free graph `G = (V, E)` (no induced `K₁,₃`) and a positive integer `K ≤ |V|`.
QUESTION: can `V` be partitioned into `k ≤ K` disjoint sets `V₁, …, V_k` such that each `Vᵢ`
induces a complete subgraph of `G`?

This is PARTITION INTO CLIQUES ([GT15], `PartitionIntoCliquesWanted`) restricted to claw-free
graphs. The 2022 revision of Johnson's table by de Figueiredo, de Melo, Sasaki and Silva lists
the entry as NP-complete, citing Maffray and Preissmann, and gives the argument: CHROMATIC NUMBER
is NP-complete for triangle-free graphs already with 3 colours (Maffray and Preissmann), and the
complement of a triangle-free graph has no independent set of more than 2 vertices, so it is
claw-free. A partition of the complement into at most `K` cliques is the same as a proper
colouring of the triangle-free graph with at most `K` colours, so complementing the graphs that
Maffray and Preissmann construct (whose vertex count is polynomial in their input) and setting
`K = 3` reduces 3-COLORABILITY to this problem. Membership in NP: a partition of the
non-isolated vertices into cliques is a certificate, since every isolated vertex is a block of
its own (the binary vertex count does not make the problem succinct), and claw-freeness is
checked in polynomial time.

The instance, the graph, the parent well-formedness condition (a simple edge list and `0 < K ≤ |V|`)
and the question are those of PARTITION INTO CLIQUES
(`PartitionIntoCliques.PartitionIntoCliquesInstance`, `PartitionIntoCliques.Graph`,
`PartitionIntoCliques.WellFormed`, `PartitionIntoCliques.PartitionIntoCliquesFeasible`: a block map
`c : V → Fin k` for some `k ≤ K` whose blocks are cliques; empty blocks are allowed and harmless);
this module adds claw-freeness to well-formedness. Claw-freeness is MathlibExt's
`SimpleGraph.IsClawFree` (from `MathlibExt.Combinatorics.SimpleGraph.ClawFreeIndependencePoly`, as
in `PolarityClawFreeWanted`): no vertex `c` with three distinct, pairwise non-adjacent neighbours
`l₁, l₂, l₃`, equivalently (`SimpleGraph.isClawFree_iff_not_isIndContained`) no induced `K₁,₃`.

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
list on the vertices `0, ..., n - 1` and `0 < K ≤ n`) whose graph is claw-free. -/
def WellFormed (i : PartitionIntoCliquesInstance) : Prop :=
  PartitionIntoCliques.WellFormed i ∧ (Graph i).IsClawFree

open Classical in
/-- PARTITION INTO CLIQUES for claw-free graphs as a decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesClawFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoCliquesInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoCliquesFeasible i)
  | none => false

/-- **PARTITION INTO CLIQUES for claw-free graphs is NP-complete.** Source: Garey and Johnson
(1979), [GT15]; Maffray and Preissmann (1996); de Figueiredo, de Melo, Sasaki and Silva (2022),
Table 1. -/
public theorem_wanted partitionIntoCliquesClawFree_npComplete :
    partitionIntoCliquesClawFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoCliquesClawFreeDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesClawFree
