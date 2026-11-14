/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH PARTITIONING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND14] GRAPH
PARTITIONING;
L. Hyafil and R. L. Rivest, "Graph partitioning and constructing optimal
decision trees are polynomial complete problems", Rapport de Recherche 33,
IRIA-Laboria, Rocquencourt (1973).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphPartitioning

/-!
# GRAPH PARTITIONING is NP-complete

INSTANCE: a graph `G = (V, E)`, weights `w(v) ∈ Z⁺` for each `v ∈ V` and `l(e) ∈ Z⁺` for each
`e ∈ E`, and positive integers `K` and `J`. QUESTION: is there a partition of `V` into disjoint
sets `V₁, V₂, ..., Vₘ` such that `∑_{v ∈ Vᵢ} w(v) ≤ K` for `1 ≤ i ≤ m` and such that if
`E' ⊆ E` is the set of edges that have their two endpoints in two different sets `Vᵢ`, then
`∑_{e ∈ E'} l(e) ≤ J`?

Vertices are `0, ..., n - 1`. A partition is given by a block label `c v` for every vertex; the
blocks are the nonempty fibres of `c` (the number `m` of blocks is free, and empty fibres add
nothing to a weight sum). Under `WellFormed` the edge list has one entry per edge, so each edge
of `E'` is counted once. Weights and lengths use the canonical binary encoding.

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
w(n - 1)`, edge list with lengths `(u, v, l({u, v}))`, `K`, `J`. -/
abbrev GraphPartitioningInstance := ℕ × List ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ

/-- Well-formedness of an instance: one positive weight per vertex, the edge list describes a
simple graph on `{0, ..., n - 1}` (no self-loops, no edge listed twice in either orientation)
with positive lengths, and `0 < K`, `0 < J`. -/
def WellFormed (i : GraphPartitioningInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ x ∈ i.2.1, 0 < x) ∧
    (i.2.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    (∀ e ∈ i.2.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧ 0 < e.2.2 ∧
      (e.2.1, e.1) ∉ i.2.2.1.map fun e => (e.1, e.2.1)) ∧
    0 < i.2.2.2.1 ∧ 0 < i.2.2.2.2

/-- A partition into blocks (the fibres of a labelling `c`) in which every block has total
vertex weight at most `K`, and the edges whose endpoints lie in different blocks have total
length at most `J`. -/
def GraphPartitioningFeasible (i : GraphPartitioningInstance) : Prop :=
  ∃ c : ℕ → ℕ,
    (∀ b, ∑ v ∈ (Finset.range i.1).filter (fun v => c v = b), i.2.1.getD v 0 ≤
      i.2.2.2.1) ∧
    ((i.2.2.1.filter fun e => decide (c e.1 ≠ c e.2.1)).map fun e => e.2.2).sum ≤ i.2.2.2.2

open Classical in
/-- GRAPH PARTITIONING as a decision problem over bitstrings. -/
noncomputable def graphPartitioningDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphPartitioningInstance) x with
  | some i => decide (WellFormed i ∧ GraphPartitioningFeasible i)
  | none => false

/-- **GRAPH PARTITIONING is NP-complete.** Source: Garey and Johnson (1979), [ND14];
Hyafil and Rivest (1973). -/
public theorem_wanted graphPartitioning_npComplete :
    graphPartitioningDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphPartitioningDec

end MetaMathlibExt.Complexity.NPComplete.GraphPartitioning
