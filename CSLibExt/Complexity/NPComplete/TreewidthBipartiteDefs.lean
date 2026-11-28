/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREEWIDTH OF BIPARTITE GRAPHS: definitions

Source:
H. L. Bodlaender, É. Bonnet, L. Jaffke, D. Knop, P. T. Lima, M. Milanič, S. Ordyniak, S. Pandey
and O. Suchý, "Treewidth is NP-complete on cubic graphs", Electronic Journal of Combinatorics
32(3) (2025), #P3.36, doi:10.37236/13205 (arXiv:2301.10031, "Treewidth is NP-complete on cubic
graphs (and related results)", Section 1: "As the treewidth of a graph (without parallel edges)
does not change under subdivision of edges, it easily follows and is well known that Treewidth
is NP-complete on bipartite graphs");
H. L. Bodlaender, "A tourist guide through treewidth", Acta Cybernetica 11 (1993), 1-21
(Table 1: TREEWIDTH is NP-complete on bipartite graphs);
S. Arnborg, D. G. Corneil and A. Proskurowski, "Complexity of finding embeddings in a k-tree",
SIAM Journal on Algebraic and Discrete Methods 8 (1987), 277-284, doi:10.1137/0608024 (TREEWIDTH
on arbitrary graphs).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TreewidthDefs
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreewidthBipartite

open MetaMathlibExt.Complexity.NPComplete.Treewidth

/-- Well-formedness of an instance: a well-formed TREEWIDTH instance (simple edge list) whose
graph is bipartite: its vertices split into two independent sets. -/
def BipartiteWellFormed (i : TreewidthInstance) : Prop :=
  WellFormed i ∧ (Graph i).IsBipartite

open Classical in
/-- TREEWIDTH OF BIPARTITE GRAPHS as a decision problem over bitstrings. -/
noncomputable def treewidthBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreewidthInstance) x with
  | some i => decide (BipartiteWellFormed i ∧ TreewidthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TreewidthBipartite
