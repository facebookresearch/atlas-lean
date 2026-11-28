/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE CHOICE MATCHING (bipartite, classes of at most 2 edges, K = |V|/2): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT55] MULTIPLE CHOICE MATCHING,
p. 203 (comment: "Remains NP-complete even if `G` is bipartite, each `Eᵢ` contains at most 2
edges, and `K = |V|/2`."), crediting [Valiant, 1977c], [Itai and Rodeh, 1977a] and
[Itai, Rodeh, and Tanimoto, 1978];
A. Itai, M. Rodeh and S. L. Tanimoto, "Some matching problems for bipartite graphs",
Journal of the ACM 25 (1978), 517-525, doi:10.1145/322092.322093;
A. Itai and M. Rodeh, "Some matching problems", Automata, Languages and Programming (ICALP
1977), Lecture Notes in Computer Science 52, Springer (1977), 258-268,
doi:10.1007/3-540-08342-1_20.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import CSLibExt.Complexity.NPComplete.MultipleChoiceMatchingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleChoiceMatchingBipartite

open MultipleChoiceMatching (MultipleChoiceMatchingInstance Graph
  MultipleChoiceMatchingFeasible)

/-- Well-formedness of an instance: the parent's (a simple edge list in range, each edge
listed once with one class label, `K` positive), the graph is bipartite, every class contains
at most 2 edges, and `K = |V|/2`. -/
def WellFormed (i : MultipleChoiceMatchingInstance) : Prop :=
  MultipleChoiceMatching.WellFormed i ∧ (Graph i).IsBipartite ∧
    (∀ c, (i.2.1.filter fun e => e.2.2 = c).length ≤ 2) ∧ 2 * i.2.2 = i.1

open Classical in
/-- MULTIPLE CHOICE MATCHING restricted to bipartite graphs, classes of at most 2 edges and
`K = |V|/2`, as a decision problem over bitstrings. -/
noncomputable def multipleChoiceMatchingBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipleChoiceMatchingInstance) x with
  | some i => decide (WellFormed i ∧ MultipleChoiceMatchingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipleChoiceMatchingBipartite
