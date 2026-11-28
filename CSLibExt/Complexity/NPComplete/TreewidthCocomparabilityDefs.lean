/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREEWIDTH OF COCOMPARABILITY GRAPHS: definitions

Source:
H. L. Bodlaender, "A tourist guide through treewidth", Acta Cybernetica 11 (1993), 1-21
(Table 1: TREEWIDTH is NP-complete on cocomparability graphs, citing Arnborg, Corneil and
Proskurowski and Habib and Möhring);
S. Arnborg, D. G. Corneil and A. Proskurowski, "Complexity of finding embeddings in a k-tree",
SIAM Journal on Algebraic and Discrete Methods 8 (1987), 277-284, doi:10.1137/0608024;
M. Habib and R. H. Möhring, "Treewidth of cocomparability graphs and a new order-theoretic
parameter", Order 11 (1994), 47-60, doi:10.1007/BF01462229;
H. L. Bodlaender, É. Bonnet, L. Jaffke, D. Knop, P. T. Lima, M. Milanič, S. Ordyniak, S. Pandey
and O. Suchý, "Treewidth is NP-complete on cubic graphs", Electronic Journal of Combinatorics
32(3) (2025), #P3.36, doi:10.37236/13205 (arXiv:2301.10031, Corollary 3.2: "Treewidth is
NP-complete on co-bipartite graphs", attributed in Section 1 to Arnborg, Corneil and
Proskurowski).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ComparabilityGraphSandwichDefs
public import CSLibExt.Complexity.NPComplete.TreewidthDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreewidthCocomparability

open MetaMathlibExt.Complexity.NPComplete.Treewidth

/-- Well-formedness of an instance: a well-formed TREEWIDTH instance (simple edge list) whose
graph is a cocomparability graph: its complement is a comparability graph. -/
def CocomparabilityWellFormed (i : TreewidthInstance) : Prop :=
  WellFormed i ∧ ComparabilityGraphSandwich.IsComparabilityGraph (Graph i)ᶜ

open Classical in
/-- TREEWIDTH OF COCOMPARABILITY GRAPHS as a decision problem over bitstrings. -/
noncomputable def treewidthCocomparabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreewidthInstance) x with
  | some i => decide (CocomparabilityWellFormed i ∧ TreewidthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TreewidthCocomparability
