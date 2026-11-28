/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE CHOICE BRANCHING on strongly connected digraphs with equal weights: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND11] MULTIPLE CHOICE BRANCHING, p. 208,
comment: "Remains NP-complete even if G is strongly connected and all weights are equal" (the
entry's reference is [Garey and Johnson, ——], unpublished; transformation from 3SAT).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultipleChoiceBranchingDefs
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleChoiceBranchingStronglyConnectedEqualWeights

open MetaMathlibExt.Complexity.NPComplete.MultipleChoiceBranching
  (MultipleChoiceBranchingInstance MultipleChoiceBranchingFeasible)

/-- `G` is strongly connected: every vertex reaches every vertex along arcs of `G`. -/
def StronglyConnected (i : MultipleChoiceBranchingInstance) : Prop :=
  ∀ u < i.1, ∀ v < i.1, Relation.ReflTransGen (fun x y => ∃ a ∈ i.2.1, a.1 = x ∧ a.2.1 = y) u v

/-- Well-formedness of an instance: a well-formed MULTIPLE CHOICE BRANCHING instance whose
digraph is strongly connected and whose arcs all have the same weight. -/
def WellFormed (i : MultipleChoiceBranchingInstance) : Prop :=
  MultipleChoiceBranching.WellFormed i ∧ StronglyConnected i ∧
    ∀ a ∈ i.2.1, ∀ b ∈ i.2.1, a.2.2.1 = b.2.2.1

open Classical in
/-- MULTIPLE CHOICE BRANCHING on strongly connected digraphs with equal weights as a decision
problem over bitstrings. -/
noncomputable def multipleChoiceBranchingStronglyConnectedEqualWeightsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MultipleChoiceBranchingInstance) x with
  | some i => decide (WellFormed i ∧ MultipleChoiceBranchingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipleChoiceBranchingStronglyConnectedEqualWeights
