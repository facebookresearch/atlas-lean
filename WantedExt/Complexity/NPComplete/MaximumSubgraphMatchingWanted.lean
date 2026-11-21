/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM SUBGRAPH MATCHING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT50] MAXIMUM
SUBGRAPH MATCHING (attributed there to Garey and Johnson, unpublished;
transformation from CLIQUE).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.Digraph.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumSubgraphMatching

/-!
# MAXIMUM SUBGRAPH MATCHING is NP-complete

INSTANCE: directed graphs `G = (V₁, A₁)`, `H = (V₂, A₂)`, and a positive integer `K`.
QUESTION: is there a subset `R ⊆ V₁ × V₂` with `|R| ≥ K` such that, for all `⟨u, u'⟩` and
`⟨v, v'⟩` in `R`, `(u, v) ∈ A₁` if and only if `(u', v') ∈ A₂`?

`R` is an arbitrary relation: it need not be injective or a function in either coordinate,
exactly as in the source. Directed graphs are given by arc lists without loops or repeated
arcs, and are read as Mathlib `Digraph`s.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n₁` of `G` (vertices `Fin n₁`), arc list of `G`, vertex count
`n₂` of `H` (vertices `Fin n₂`), arc list of `H`, and the bound `K`. -/
abbrev MaximumSubgraphMatchingInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ) × ℕ

/-- The directed graph on `Fin n` whose arcs are the pairs listed in `as`. -/
def digraphOfArcs (n : ℕ) (as : List (ℕ × ℕ)) : Digraph (Fin n) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ as

/-- The first directed graph `G = (V₁, A₁)`. -/
def GraphG (i : MaximumSubgraphMatchingInstance) : Digraph (Fin i.1) :=
  digraphOfArcs i.1 i.2.1

/-- The second directed graph `H = (V₂, A₂)`. -/
def GraphH (i : MaximumSubgraphMatchingInstance) : Digraph (Fin i.2.2.1) :=
  digraphOfArcs i.2.2.1 i.2.2.2.1

/-- Well-formedness of an instance: each arc list has no repeated arcs, no loops, and
endpoints in range, and `K` is positive. -/
def WellFormed (i : MaximumSubgraphMatchingInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2) ∧
    (i.2.2.2.1.Nodup ∧ ∀ e ∈ i.2.2.2.1, e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2) ∧
    0 < i.2.2.2.2

/-- A relation `R ⊆ V₁ × V₂` with at least `K` pairs such that for all `⟨u, u'⟩, ⟨v, v'⟩ ∈ R`,
`(u, v)` is an arc of `G` iff `(u', v')` is an arc of `H`. -/
def MaximumSubgraphMatchingFeasible (i : MaximumSubgraphMatchingInstance) : Prop :=
  ∃ R : Finset (Fin i.1 × Fin i.2.2.1), i.2.2.2.2 ≤ R.card ∧
    ∀ p ∈ R, ∀ q ∈ R, ((GraphG i).Adj p.1 q.1 ↔ (GraphH i).Adj p.2 q.2)

open Classical in
/-- MAXIMUM SUBGRAPH MATCHING as a decision problem over bitstrings. -/
noncomputable def maximumSubgraphMatchingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumSubgraphMatchingInstance) x with
  | some i => decide (WellFormed i ∧ MaximumSubgraphMatchingFeasible i)
  | none => false

/-- **MAXIMUM SUBGRAPH MATCHING is NP-complete.** Source: Garey and Johnson (1979), [GT50]. -/
public theorem_wanted maximumSubgraphMatching_npComplete :
    maximumSubgraphMatchingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumSubgraphMatchingDec

end MetaMathlibExt.Complexity.NPComplete.MaximumSubgraphMatching
