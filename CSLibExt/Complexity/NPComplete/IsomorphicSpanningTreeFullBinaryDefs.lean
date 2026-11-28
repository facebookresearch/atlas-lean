/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ISOMORPHIC SPANNING TREE for full binary trees: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND8] ISOMORPHIC SPANNING TREE
(p. 207), comment "Remains NP-complete even if ... (b) T is a full binary tree [Papadimitriou
and Yannakakis, 1978]";
C. H. Papadimitriou and M. Yannakakis, "The complexity of restricted spanning tree problems",
Journal of the ACM 29(2) (1982), 285-309, doi:10.1145/322307.322309.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Set.Card
public import CSLibExt.Complexity.NPComplete.IsomorphicSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IsomorphicSpanningTreeFullBinary

open MetaMathlibExt.Complexity.NPComplete.IsomorphicSpanningTree

/-- `T` is a full binary tree: a tree that, rooted at a suitable vertex, has one vertex, or a
root `r` of degree `2` with every other vertex of degree `1` or `3`. -/
def IsFullBinary {m : ℕ} (T : SimpleGraph (Fin m)) : Prop :=
  T.IsTree ∧ (m = 1 ∨ ∃ r : Fin m, (T.neighborSet r).ncard = 2 ∧
    ∀ v, v ≠ r → (T.neighborSet v).ncard = 1 ∨ (T.neighborSet v).ncard = 3)

/-- Well-formedness of an instance: the parent's (simple edge lists, `T` a tree), and `T` is a
full binary tree (which repeats the tree condition). -/
def WellFormed (i : IsomorphicSpanningTreeInstance) : Prop :=
  IsomorphicSpanningTree.WellFormed i ∧ IsFullBinary (TreeGraph i)

open Classical in
/-- ISOMORPHIC SPANNING TREE for full binary trees as a decision problem over bitstrings. -/
noncomputable def isomorphicSpanningTreeFullBinaryDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IsomorphicSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ IsomorphicSpanningTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IsomorphicSpanningTreeFullBinary
