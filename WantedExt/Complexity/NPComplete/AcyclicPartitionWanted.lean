/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACYCLIC PARTITION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND15] ACYCLIC
PARTITION (credited there to Garey and Johnson, unpublished; transformation from
X3C).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AcyclicPartition

/-!
# ACYCLIC PARTITION is NP-complete

INSTANCE: a directed graph `G = (V, A)`, a weight `w(v) ∈ Z⁺` for each `v ∈ V`, a cost
`c(a) ∈ Z⁺` for each `a ∈ A`, and positive integers `B` and `K`. QUESTION: is there a partition
of `V` into disjoint sets `V₁, ..., Vₘ` such that the directed graph `G' = (V', A')`, where
`V' = {V₁, ..., Vₘ}` and `(Vᵢ, Vⱼ) ∈ A'` if and only if `(vᵢ, vⱼ) ∈ A` for some `vᵢ ∈ Vᵢ` and some
`vⱼ ∈ Vⱼ` (`i ≠ j`), is acyclic, such that the sum of the weights of the vertices in each `Vᵢ`
does not exceed `B`, and such that the sum of the costs of all those arcs having their
endpoints in different sets does not exceed `K`?

Vertices are `0, ..., n - 1`. A partition is given by a block label `p v` for every vertex;
the blocks are the nonempty fibres of `p`. `quotientArc` is the arc relation of `G'` on block
labels (arcs inside one block give no arc of `G'`), and "acyclic" is the absence of a directed
cycle: no block reaches itself by a nonempty `Relation.TransGen` path. Weights and costs use the
canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), vertex weights `w(0), ...,
w(n - 1)`, arc list with costs `(u, v, c((u, v)))`, `B`, `K`. -/
abbrev AcyclicPartitionInstance := ℕ × List ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ

/-- Well-formedness of an instance: one positive weight per vertex, the arc list describes a
directed graph on `{0, ..., n - 1}` (no self-loops, no arc listed twice) with positive costs,
and `0 < B`, `0 < K`. -/
def WellFormed (i : AcyclicPartitionInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ x ∈ i.2.1, 0 < x) ∧
    (i.2.2.1.map fun a => (a.1, a.2.1)).Nodup ∧
    (∀ a ∈ i.2.2.1, a.1 < i.1 ∧ a.2.1 < i.1 ∧ a.1 ≠ a.2.1 ∧ 0 < a.2.2) ∧
    0 < i.2.2.2.1 ∧ 0 < i.2.2.2.2

/-- The arcs of the quotient digraph `G'` on block labels: `b₁ → b₂` when `b₁ ≠ b₂` and some
arc of `G` goes from block `b₁` to block `b₂`. -/
def quotientArc (i : AcyclicPartitionInstance) (p : ℕ → ℕ) (b₁ b₂ : ℕ) : Prop :=
  b₁ ≠ b₂ ∧ ∃ a ∈ i.2.2.1, p a.1 = b₁ ∧ p a.2.1 = b₂

/-- A partition into blocks (the fibres of a labelling `p`) whose quotient digraph has no
directed cycle, in which every block has total vertex weight at most `B`, and the arcs whose
endpoints lie in different blocks have total cost at most `K`. -/
def AcyclicPartitionFeasible (i : AcyclicPartitionInstance) : Prop :=
  ∃ p : ℕ → ℕ,
    (∀ b, ¬ Relation.TransGen (quotientArc i p) b b) ∧
    (∀ b, ∑ v ∈ (Finset.range i.1).filter (fun v => p v = b), i.2.1.getD v 0 ≤
      i.2.2.2.1) ∧
    ((i.2.2.1.filter fun a => decide (p a.1 ≠ p a.2.1)).map fun a => a.2.2).sum ≤ i.2.2.2.2

open Classical in
/-- ACYCLIC PARTITION as a decision problem over bitstrings. -/
noncomputable def acyclicPartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AcyclicPartitionInstance) x with
  | some i => decide (WellFormed i ∧ AcyclicPartitionFeasible i)
  | none => false

/-- **ACYCLIC PARTITION is NP-complete.** Source: Garey and Johnson (1979), [ND15]. -/
public theorem_wanted acyclicPartition_npComplete :
    acyclicPartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L acyclicPartitionDec

end MetaMathlibExt.Complexity.NPComplete.AcyclicPartition
