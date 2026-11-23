/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BINARY TREE ∩ PARTIAL GRID RECOGNITION is NP-complete

Source:
A. Gregori, "Unit-length embedding of binary trees on a square grid", Information Processing
Letters 31 (1989), 167-173, doi:10.1016/0020-0190(89)90118-X (original not available here);
V. G. P. de Sá, G. D. da Fonseca, R. C. S. Machado and C. M. H. de Figueiredo, "Complexity
dichotomy on partial grid recognition", Theoretical Computer Science 412 (2011), 2370-2379,
doi:10.1016/j.tcs.2011.01.018 (arXiv:1006.3541; abstract: deciding whether a graph can be
embedded in a grid using only unit-length edges "is NP-complete, even when restricted to binary
trees"; Section 2: "The NP-completeness for {1,2,3}-trees (binary trees) was demonstrated by
Gregori");
ISGCI, class "binary tree ∩ partial grid" (gc_848), problem Recognition, NP-complete, citing both.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UnitLengthTreeGridEmbeddingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BinaryTreePartialGridRecognition

open MetaMathlibExt.Complexity.NPComplete.UnitLengthTreeGridEmbedding
  (UnitLengthTreeGridEmbeddingInstance Graph)

/-!
# BINARY TREE ∩ PARTIAL GRID RECOGNITION is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is `G` a binary tree that is a partial grid, i.e., a
tree with every vertex of degree at most `3` that is isomorphic to a (not necessarily induced)
subgraph of the infinite square grid?

ISGCI defines the classes: "A tree is a binary tree if every vertex has degree at most 3"
(gc_847), and "A graph is a partial grid iff it is an arbitrary subgraph (not necessarily
induced) of a grid" (gc_440). Gregori proved that deciding whether a binary tree is a partial
grid (has a unit-length embedding in the square grid) is NP-complete; de Sá et al. record the
result and call these trees `{1,2,3}`-trees.

This is the restriction of the merged `UnitLengthTreeGridEmbeddingWanted` (UNIT-LENGTH TREE
EMBEDDING IN THE GRID, for all trees) to binary trees. The instance, the graph and the question
are reused unchanged: an edge list on `Fin n` (`UnitLengthTreeGridEmbeddingInstance`,
`UnitLengthTreeGridEmbedding.Graph`), and
`UnitLengthTreeGridEmbedding.UnitLengthTreeGridEmbeddingFeasible`: the graph is contained
(Mathlib's `SimpleGraph.IsContained`, an injective edge-preserving map) in the infinite square
grid `StatMech.Lattice.hypercubicLattice 2`. Well-formedness is the parent's
`UnitLengthTreeGridEmbedding.WellFormed` (a simple edge list whose graph is a Mathlib
`SimpleGraph.IsTree`) plus the degree bound: every vertex has at most `3` neighbors
(`(Graph i).neighborSet v` has `Set.ncard` at most `3`). Since an input that is not a binary tree
is a no-instance, this decision problem is the recognition problem for the class on arbitrary
graphs.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed instance of `UnitLengthTreeGridEmbeddingWanted`
(a simple edge list whose graph is a tree) in which every vertex has degree at most `3`. -/
def WellFormed (i : UnitLengthTreeGridEmbeddingInstance) : Prop :=
  UnitLengthTreeGridEmbedding.WellFormed i ∧ ∀ v : Fin i.1, ((Graph i).neighborSet v).ncard ≤ 3

open Classical in
/-- BINARY TREE ∩ PARTIAL GRID RECOGNITION as a decision problem over bitstrings. -/
noncomputable def binaryTreePartialGridRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitLengthTreeGridEmbeddingInstance) x with
  | some i =>
    decide (WellFormed i ∧ UnitLengthTreeGridEmbedding.UnitLengthTreeGridEmbeddingFeasible i)
  | none => false

/-- **BINARY TREE ∩ PARTIAL GRID RECOGNITION is NP-complete.** Source: Gregori (1989); de Sá,
da Fonseca, Machado and de Figueiredo (2011). -/
public theorem_wanted binaryTreePartialGridRecognition_npComplete :
    binaryTreePartialGridRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L binaryTreePartialGridRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.BinaryTreePartialGridRecognition
