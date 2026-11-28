/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH OF COCOMPARABILITY GRAPHS: definitions

Source:
M. Habib and R. H. Möhring, "Treewidth of cocomparability graphs and a new order-theoretic
parameter", Order 11 (1994), 47-60, doi:10.1007/BF01462229 (treewidth and pathwidth coincide on
cocomparability graphs);
S. Arnborg, D. G. Corneil, and A. Proskurowski, "Complexity of finding embeddings in a k-tree",
SIAM Journal on Algebraic and Discrete Methods 8 (1987), 277-284, doi:10.1137/0608024 (NP-complete
on complements of bipartite graphs);
T. Kloks, D. Kratsch, and J. Spinrad, "Treewidth and pathwidth of cocomparability graphs of
bounded dimension", Computing Science Notes 93/46, Eindhoven University of Technology (1993)
(records both results).
-/
module

public import CSLibExt.Complexity.NPComplete.ComparabilityGraphSandwichDefs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PathwidthChordalGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathwidthCocomparabilityGraphs

open MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs
  (PathwidthChordalGraphsInstance Graph PathwidthChordalGraphsFeasible)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the complement of the
graph is a comparability graph, and `0 < K`. -/
def WellFormed (i : PathwidthChordalGraphsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    ComparabilityGraphSandwich.IsComparabilityGraph (Graph i)ᶜ ∧ 0 < i.2.2

open Classical in
/-- PATHWIDTH OF COCOMPARABILITY GRAPHS as a decision problem over bitstrings. -/
noncomputable def pathwidthCocomparabilityGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathwidthChordalGraphsInstance) x with
  | some i => decide (WellFormed i ∧ PathwidthChordalGraphsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PathwidthCocomparabilityGraphs
