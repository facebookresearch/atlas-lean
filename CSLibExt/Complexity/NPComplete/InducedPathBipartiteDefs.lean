/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDUCED PATH for bipartite graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT23] INDUCED PATH, comment ("Remains
NP-complete if G is bipartite"), attributed to M. Yannakakis, "Node- and edge-deletion
NP-complete problems", Proceedings of the 10th Annual ACM Symposium on Theory of Computing
(STOC 1978), 253-264, doi:10.1145/800133.804355.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import CSLibExt.Complexity.NPComplete.InducedPathDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InducedPathBipartite

open MetaMathlibExt.Complexity.NPComplete.InducedPath (InducedPathInstance InducedPathFeasible)

/-- Well-formedness of an instance: a well-formed INDUCED PATH instance whose graph is
bipartite. -/
def WellFormed (i : InducedPathInstance) : Prop :=
  InducedPath.WellFormed i ∧ (InducedPath.Graph i).IsBipartite

open Classical in
/-- INDUCED PATH for bipartite graphs as a decision problem over bitstrings. -/
noncomputable def inducedPathBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InducedPathInstance) x with
  | some i => decide (WellFormed i ∧ InducedPathFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.InducedPathBipartite
