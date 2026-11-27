/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE RANKING is NP-complete

Source:
T. W. Lam and F. L. Yue, "Edge ranking of graphs is hard", Discrete Applied Mathematics 85(1)
(1998), 71-86, doi:10.1016/S0166-218X(98)00029-8 (computing an optimal edge ranking of a
general graph is NP-hard).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeRanking

/-!
# EDGE RANKING is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K`.
QUESTION: does `G` have an edge ranking with at most `K` ranks, that is, a labeling
`f : E → {1, …, K}` of the edges such that every path between two distinct edges with the
same label `i` contains an edge with a label larger than `i`?

A path between two edges `e₁` and `e₂` is a path in `G` (a Mathlib `SimpleGraph.Walk` with
`IsPath`) whose first edge is `e₁` and whose last edge is `e₂`. Its other edges are the
intermediate edges, and since `e₁` and `e₂` carry the label `i`, an edge of the path with a
larger label is intermediate. Edges are elements of `Sym2 (Fin n)`; the labeling is a function
on `Sym2 (Fin n)` whose values on non-edges are irrelevant. `K` uses the canonical binary
encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, and the number of ranks `K`. -/
abbrev EdgeRankingInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : EdgeRankingInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: a simple edge list on `Fin n` (no repeated edge, no loop,
no reversed copy), and `K` is positive. -/
def WellFormed (i : EdgeRankingInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- `f` is an edge ranking of `G`: for every path whose first edge `e₁` and last edge `e₂` are
distinct and have the same label, some edge of the path has a larger label. -/
def IsEdgeRanking {n : ℕ} (G : SimpleGraph (Fin n)) (f : Sym2 (Fin n) → ℕ) : Prop :=
  ∀ (u v : Fin n) (p : G.Walk u v), p.IsPath → ∀ e₁ e₂ : Sym2 (Fin n),
    p.edges.head? = some e₁ → p.edges.getLast? = some e₂ → e₁ ≠ e₂ → f e₁ = f e₂ →
      ∃ e ∈ p.edges, f e₁ < f e

/-- Some labeling of the edges with labels in `{1, …, K}` is an edge ranking. -/
def EdgeRankingFeasible (i : EdgeRankingInstance) : Prop :=
  ∃ f : Sym2 (Fin i.1) → ℕ, (∀ e ∈ (Graph i).edgeSet, 1 ≤ f e ∧ f e ≤ i.2.2) ∧
    IsEdgeRanking (Graph i) f

open Classical in
/-- EDGE RANKING as a decision problem over bitstrings. -/
noncomputable def edgeRankingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgeRankingInstance) x with
  | some i => decide (WellFormed i ∧ EdgeRankingFeasible i)
  | none => false

/-- **EDGE RANKING is NP-complete.** Source: Lam and Yue (1998). -/
public theorem_wanted edgeRanking_npComplete :
    edgeRankingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L edgeRankingDec

end MetaMathlibExt.Complexity.NPComplete.EdgeRanking
