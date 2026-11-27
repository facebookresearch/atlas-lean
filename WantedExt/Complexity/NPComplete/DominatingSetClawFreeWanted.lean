/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET for claw-free graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET, comment (EDGE
DOMINATING SET "is NP-complete, even for planar or bipartite graphs of maximum degree 3");
M. Yannakakis and F. Gavril, "Edge dominating sets in graphs", SIAM Journal on Applied
Mathematics 38 (1980), 364-372, doi:10.1137/0138030;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021,
Table 1 (DOMINATING SET on CLAW-FREE: N [GJ]).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Combinatorics.SimpleGraph.ClawFreeIndependencePoly
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetClawFree

open DominatingSet (DominatingSetInstance Graph DominatingSetFeasible)

/-!
# DOMINATING SET for claw-free graphs is NP-complete

INSTANCE: a claw-free graph `G = (V, E)` (no induced `K₁,₃`) and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set of size at most `K`, i.e. `V' ⊆ V` with `|V'| ≤ K` such that
every vertex outside `V'` has a neighbour in `V'`?

This is DOMINATING SET ([GT2], `DominatingSetDefs`) restricted to claw-free graphs. Johnson's
1985 table (NP-completeness column 16) and its 2022 revision list it as NP-complete with the
reference [GJ]: Garey and Johnson's comment to [GT2] records that EDGE DOMINATING SET is
NP-complete (Yannakakis and Gavril), and an edge dominating set of `H` is exactly a dominating set
of the line graph `L(H)`, which is claw-free. The instance type, the graph, the parent's
well-formedness (a simple edge list) and the question are the parent's; the restriction adds
claw-freeness and Garey and Johnson's bound `0 < K ≤ |V|` to `WellFormed`, as in
`DominatingSetSplitGraphsWanted`.
Claw-freeness is the repository's predicate `SimpleGraph.IsClawFree` (from
`MathlibExt.Combinatorics.SimpleGraph.ClawFreeIndependencePoly`, as in `PolarityClawFreeWanted`):
no vertex `c` with three distinct, pairwise non-adjacent neighbours `l₁, l₂, l₃`, i.e. no induced
`K₁,₃`.

Membership in NP holds for all graphs, and claw-freeness is checked in `O(n⁴)` time. Every
isolated vertex lies in every dominating set, so an instance reduces to the subgraph on the
vertices that occur in edges, with the bound lowered by the number of isolated vertices; the
certificate is a dominating set of that subgraph, and the binary vertex count does not make the
problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed DOMINATING SET instance (a simple edge list on
`Fin n`) whose graph is claw-free, and `0 < K ≤ n`. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ (Graph i).IsClawFree ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- DOMINATING SET for claw-free graphs as a decision problem
over bitstrings. -/
noncomputable def dominatingSetClawFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

/-- **DOMINATING SET for claw-free graphs is NP-complete.**
Source: Garey and Johnson (1979), [GT2]; Yannakakis and Gavril (1980). -/
public theorem_wanted dominatingSetClawFree_npComplete :
    dominatingSetClawFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetClawFreeDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetClawFree
