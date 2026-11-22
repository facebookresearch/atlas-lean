/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE CHOICE BRANCHING on strongly connected digraphs with equal weights is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND11] MULTIPLE CHOICE BRANCHING, p. 208,
comment: "Remains NP-complete even if G is strongly connected and all weights are equal" (the
entry's reference is [Garey and Johnson, ——], unpublished; transformation from 3SAT).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultipleChoiceBranchingWanted
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleChoiceBranchingStronglyConnectedEqualWeights

open MetaMathlibExt.Complexity.NPComplete.MultipleChoiceBranching
  (MultipleChoiceBranchingInstance MultipleChoiceBranchingFeasible)

/-!
# MULTIPLE CHOICE BRANCHING on strongly connected digraphs with equal weights is NP-complete

INSTANCE: a strongly connected directed graph `G = (V, A)`, a weight `w(a) ∈ Z⁺` for each arc
`a ∈ A`, all weights equal, a partition of `A` into disjoint sets `A₁, A₂, …, A_m`, and a
positive integer `K`.
QUESTION: is there a subset `A' ⊆ A` with `∑_{a ∈ A'} w(a) ≥ K` such that no two arcs in `A'`
enter the same vertex, `A'` contains no cycles, and `A'` contains at most one arc from each of
the `Aᵢ`, `1 ≤ i ≤ m`?

The instance, `WellFormed` (arcs `(u, v, w, class)` on `{0, …, n - 1}` without loops or
repeated arcs, positive weights, `0 < K`) and the question are those of
`MultipleChoiceBranchingWanted` ([ND11]). This module adds to well-formedness:

* strong connectivity: every vertex `u < n` reaches every vertex `v < n` along arcs
  (`Relation.ReflTransGen` of the arc relation, the relation whose `TransGen` the parent uses
  for cycles);
* equal weights: any two arcs have the same weight.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **MULTIPLE CHOICE BRANCHING on strongly connected digraphs with equal weights is
NP-complete.** Source: Garey and Johnson (1979), [ND11], comment. -/
public theorem_wanted multipleChoiceBranchingStronglyConnectedEqualWeights_npComplete :
    multipleChoiceBranchingStronglyConnectedEqualWeightsDec ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipleChoiceBranchingStronglyConnectedEqualWeightsDec

end MetaMathlibExt.Complexity.NPComplete.MultipleChoiceBranchingStronglyConnectedEqualWeights
