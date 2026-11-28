/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BINARY TREE ∩ PARTIAL GRID RECOGNITION: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnitLengthTreeGridEmbeddingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BinaryTreePartialGridRecognition

open MetaMathlibExt.Complexity.NPComplete.UnitLengthTreeGridEmbedding
  (UnitLengthTreeGridEmbeddingInstance Graph)

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

end MetaMathlibExt.Complexity.NPComplete.BinaryTreePartialGridRecognition
