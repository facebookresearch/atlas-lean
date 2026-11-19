/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS with unit weights, terminals forming one side of a bipartite graph,
is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS,
p. 209 (comment: "Remains NP-complete if all edge weights are equal, even if G is a bipartite
graph having no edges joining two vertices in R or two vertices in V−R [Berlekamp, 1976]").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SteinerTreeBipartiteWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeBipartiteTerminalSide

open SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-!
# STEINER TREE IN GRAPHS with unit weights, terminals forming one side of a bipartite graph,
is NP-complete

INSTANCE: a bipartite graph `G = (V, E)` with all edge weights equal to 1 and no edge joining two
vertices in `R` or two vertices in `V − R`, a subset `R ⊆ V`, and a positive integer `B`.
QUESTION: is there a subtree of `G` that includes all the vertices of `R` and has at most `B`
edges?

This restricts `WantedExt.Complexity.NPComplete.SteinerTreeBipartiteWanted` (STEINER TREE IN
GRAPHS with unit weights on bipartite graphs) to the stronger restriction of Garey and Johnson's
comment: every edge joins a vertex of `R` to a vertex of `V − R`. The instance type and the
question `SteinerTree.SteinerTreeFeasible` of [ND12] (`SteinerTreeWanted`) are reused unchanged,
and `WellFormed` extends `SteinerTreeBipartite.WellFormed` (the [ND12] well-formedness, unit
weights, a bipartite graph, `0 < n`, `0 < B`) with that condition; it makes `R`, `V − R` a
bipartition, so the bipartite conjunct is implied but kept for the reuse.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the bipartite unit-weight condition of
`SteinerTreeBipartite`, and every edge has exactly one endpoint in `R`. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  SteinerTreeBipartite.WellFormed i ∧ ∀ e ∈ i.2.1, (e.1 ∈ i.2.2.1 ↔ e.2.1 ∉ i.2.2.1)

open Classical in
/-- STEINER TREE IN GRAPHS with unit weights and terminals forming one side of a bipartite
graph, as a decision problem over bitstrings. -/
noncomputable def steinerTreeBipartiteTerminalSideDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible i)
  | none => false

/-- **STEINER TREE IN GRAPHS with unit weights, terminals forming one side of a bipartite graph,
is NP-complete.** Source: Garey and Johnson (1979), [ND12], comment (Berlekamp, 1976). -/
public theorem_wanted steinerTreeBipartiteTerminalSide_npComplete :
    steinerTreeBipartiteTerminalSideDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L steinerTreeBipartiteTerminalSideDec

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeBipartiteTerminalSide
