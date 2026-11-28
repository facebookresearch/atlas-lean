/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS with unit weights, terminals forming one side of a bipartite graph:
definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS,
p. 209 (comment: "Remains NP-complete if all edge weights are equal, even if G is a bipartite
graph having no edges joining two vertices in R or two vertices in V−R [Berlekamp, 1976]").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SteinerTreeBipartiteDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeBipartiteTerminalSide

open SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

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

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeBipartiteTerminalSide
