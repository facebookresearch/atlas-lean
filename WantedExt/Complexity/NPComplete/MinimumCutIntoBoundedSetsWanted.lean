/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM CUT INTO BOUNDED SETS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND17] MINIMUM CUT INTO
BOUNDED SETS;
M. R. Garey, D. S. Johnson, and L. Stockmeyer, "Some simplified NP-complete graph
problems", Theoretical Computer Science 1 (1976), 237-267,
doi:10.1016/0304-3975(76)90059-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCutIntoBoundedSets

/-!
# MINIMUM CUT INTO BOUNDED SETS is NP-complete

INSTANCE: a graph `G = (V, E)`, a weight `w(e) ∈ Z⁺` for each `e ∈ E`, specified vertices
`s, t ∈ V`, a positive integer `B ≤ |V|`, and a positive integer `K`. QUESTION: is there a
partition of `V` into disjoint sets `V₁` and `V₂` such that `s ∈ V₁`, `t ∈ V₂`, `|V₁| ≤ B`,
`|V₂| ≤ B`, and such that the sum of the weights of the edges from `E` that have one endpoint in
`V₁` and one endpoint in `V₂` is no more than `K`?

Vertices are `0, ..., n - 1`; the partition is given by `V₁ ⊆ {0, ..., n - 1}`, with
`V₂ = {0, ..., n - 1} \ V₁`. Under `WellFormed` the weighted edge list has one entry per edge, so
each cut edge is counted once. Weights use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), weighted edge list
`(u, v, w({u, v}))`, `s`, `t`, `B`, `K`. -/
abbrev MinimumCutIntoBoundedSetsInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ × ℕ × ℕ

/-- Well-formedness of an instance: the edge list describes a simple graph on
`{0, ..., n - 1}` (no self-loops, no edge listed twice in either orientation), every weight is
positive, `s, t < n`, `0 < B ≤ n`, and `0 < K`. -/
def WellFormed (i : MinimumCutIntoBoundedSetsInstance) : Prop :=
  (i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧ 0 < e.2.2 ∧
      (e.2.1, e.1) ∉ i.2.1.map fun e => (e.1, e.2.1)) ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧ 0 < i.2.2.2.2.1 ∧ i.2.2.2.2.1 ≤ i.1 ∧ 0 < i.2.2.2.2.2

/-- A partition `V₁`, `V₂ = {0, ..., n - 1} \ V₁` with `s ∈ V₁`, `t ∈ V₂`, `|V₁| ≤ B`,
`|V₂| ≤ B`, and total weight of the edges with one endpoint in each part at most `K`. -/
def MinimumCutIntoBoundedSetsFeasible (i : MinimumCutIntoBoundedSetsInstance) : Prop :=
  ∃ V₁ : Finset ℕ, V₁ ⊆ Finset.range i.1 ∧
    i.2.2.1 ∈ V₁ ∧ i.2.2.2.1 ∉ V₁ ∧
    V₁.card ≤ i.2.2.2.2.1 ∧ (Finset.range i.1 \ V₁).card ≤ i.2.2.2.2.1 ∧
    ((i.2.1.filter fun e =>
        decide ((e.1 ∈ V₁ ∧ e.2.1 ∉ V₁) ∨ (e.1 ∉ V₁ ∧ e.2.1 ∈ V₁))).map fun e => e.2.2).sum ≤
      i.2.2.2.2.2

open Classical in
/-- MINIMUM CUT INTO BOUNDED SETS as a decision problem over bitstrings. -/
noncomputable def minimumCutIntoBoundedSetsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumCutIntoBoundedSetsInstance) x with
  | some i => decide (WellFormed i ∧ MinimumCutIntoBoundedSetsFeasible i)
  | none => false

/-- **MINIMUM CUT INTO BOUNDED SETS is NP-complete.** Source: Garey and Johnson (1979), [ND17];
Garey, Johnson, and Stockmeyer (1976). -/
public theorem_wanted minimumCutIntoBoundedSets_npComplete :
    minimumCutIntoBoundedSetsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumCutIntoBoundedSetsDec

end MetaMathlibExt.Complexity.NPComplete.MinimumCutIntoBoundedSets
