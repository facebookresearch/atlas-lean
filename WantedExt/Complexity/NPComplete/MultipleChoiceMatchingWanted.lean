/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE CHOICE MATCHING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT55] MULTIPLE CHOICE MATCHING;
A. Itai, M. Rodeh and S. L. Tanimoto, "Some matching problems for bipartite graphs",
Journal of the ACM 25 (1978), 517-525, doi:10.1145/322092.322093;
A. Itai and M. Rodeh, "Some matching problems", Automata, Languages and Programming (ICALP
1977), Lecture Notes in Computer Science 52, Springer (1977), 258-268,
doi:10.1007/3-540-08342-1_20.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Matching

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleChoiceMatching

/-!
# MULTIPLE CHOICE MATCHING is NP-complete

Given a graph `G = (V, E)`, a partition of `E` into disjoint sets `E₁, E₂, ..., E_J`, and a
positive integer `K`, is there a subset `E' ⊆ E` with `|E'| ≥ K` such that no two edges in
`E'` share a common vertex and such that `E'` contains at most one edge from each `Eᵢ`?

The vertices are `0, ..., n - 1`. Each edge is listed once, as a triple `(u, v, c)` saying
that the edge `{u, v}` lies in the class `E_c`; the classes are the sets of edges sharing a
label, so the labels give a partition of `E` into disjoint sets. The subset `E'` is the edge
set of a subgraph `M` of `G` that is a matching (`SimpleGraph.Subgraph.IsMatching`), which
holds exactly when no two of its edges share a vertex.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n`, the edges as triples `(u, v, c)` (edge `{u, v}` in class
`E_c`), and the bound `K`. -/
abbrev MultipleChoiceMatchingInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ

/-- The edge list of the instance, without class labels. -/
def edgeList (i : MultipleChoiceMatchingInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun e => (e.1, e.2.1)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MultipleChoiceMatchingInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (edgeList i)

/-- Well-formedness of an instance: the edge list is simple (in range, no loops, no repeated
edge in either orientation, so each edge has exactly one class), and `K` is positive. -/
def WellFormed (i : MultipleChoiceMatchingInstance) : Prop :=
  (edgeList i).Nodup ∧
    (∀ e ∈ edgeList i, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ edgeList i) ∧
      0 < i.2.2

/-- A matching of `G` with at least `K` edges and at most one edge from each class: two
listed edges with the same class that both lie in the matching are the same edge. -/
def MultipleChoiceMatchingFeasible (i : MultipleChoiceMatchingInstance) : Prop :=
  ∃ M : (Graph i).Subgraph, M.IsMatching ∧ i.2.2 ≤ M.edgeSet.ncard ∧
    ∀ e ∈ i.2.1, ∀ e' ∈ i.2.1, e.2.2 = e'.2.2 →
      (∃ (hu : e.1 < i.1) (hv : e.2.1 < i.1), M.Adj ⟨e.1, hu⟩ ⟨e.2.1, hv⟩) →
      (∃ (hu : e'.1 < i.1) (hv : e'.2.1 < i.1), M.Adj ⟨e'.1, hu⟩ ⟨e'.2.1, hv⟩) →
      e = e'

open Classical in
/-- MULTIPLE CHOICE MATCHING as a decision problem over bitstrings. -/
noncomputable def multipleChoiceMatchingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipleChoiceMatchingInstance) x with
  | some i => decide (WellFormed i ∧ MultipleChoiceMatchingFeasible i)
  | none => false

/-- **MULTIPLE CHOICE MATCHING is NP-complete.** Source: Garey and Johnson (1979), [GT55];
Itai, Rodeh and Tanimoto (1978); Itai and Rodeh (1977). -/
public theorem_wanted multipleChoiceMatching_npComplete :
    multipleChoiceMatchingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipleChoiceMatchingDec

end MetaMathlibExt.Complexity.NPComplete.MultipleChoiceMatching
