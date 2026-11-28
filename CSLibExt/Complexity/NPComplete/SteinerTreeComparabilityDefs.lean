/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS (unit weights) on comparability graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS, comment
("Remains NP-complete if all edge weights are equal, even if G is a bipartite graph having no
edges joining two vertices in R or two vertices in V-R [Berlekamp, 1976]");
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3)
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (comparability graphs, unweighted
STEINER TREE IN GRAPHS: NP-complete, citing Garey and Johnson);
H. Müller and A. Brandstädt, "The NP-completeness of Steiner tree and dominating set for chordal
bipartite graphs", Theoretical Computer Science 53(2-3) (1987), 257-265,
doi:10.1016/0304-3975(87)90067-3.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ComparabilityGraphSandwichDefs
public import CSLibExt.Complexity.NPComplete.SteinerTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeComparability

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-- Well-formedness of an instance: it is a well-formed STEINER TREE IN GRAPHS instance, every
edge has weight `1`, its graph is a comparability graph, it has at least one vertex, and the
bound `B` is positive. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    ComparabilityGraphSandwich.IsComparabilityGraph (SteinerTree.Graph i i.2.1) ∧ 0 < i.1 ∧
    0 < i.2.2.2

open Classical in
/-- STEINER TREE IN GRAPHS (unit weights) on comparability graphs as a decision problem over
bitstrings. -/
noncomputable def steinerTreeComparabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeComparability
