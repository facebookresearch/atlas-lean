/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREEWIDTH OF CO-BIPARTITE GRAPHS: definitions

Source:
S. Arnborg, D. G. Corneil and A. Proskurowski, "Complexity of finding embeddings in a k-tree",
SIAM Journal on Algebraic and Discrete Methods 8 (1987), 277-284, doi:10.1137/0608024;
H. L. Bodlaender, É. Bonnet, L. Jaffke, D. Knop, P. T. Lima, M. Milanič, S. Ordyniak, S. Pandey
and O. Suchý, "Treewidth is NP-complete on cubic graphs", Electronic Journal of Combinatorics
32(3) (2025), #P3.36, doi:10.37236/13205 (arXiv:2301.10031, "Treewidth is NP-complete on cubic
graphs (and related results)": Section 2 defines co-bipartite graphs, Corollary 3.2 states
"Treewidth is NP-complete on co-bipartite graphs", and the introduction attributes this to
Arnborg, Corneil and Proskurowski: "their proof also gives NP-completeness on co-bipartite
graphs").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TreewidthDefs
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreewidthCoBipartite

open MetaMathlibExt.Complexity.NPComplete.Treewidth

/-- Well-formedness of an instance: a well-formed TREEWIDTH instance (simple edge list) whose
graph is co-bipartite: its complement is bipartite, so its vertices split into two cliques. -/
def CoBipartiteWellFormed (i : TreewidthInstance) : Prop :=
  WellFormed i ∧ (Graph i)ᶜ.IsBipartite

open Classical in
/-- TREEWIDTH OF CO-BIPARTITE GRAPHS as a decision problem over bitstrings. -/
noncomputable def treewidthCoBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreewidthInstance) x with
  | some i => decide (CoBipartiteWellFormed i ∧ TreewidthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TreewidthCoBipartite
