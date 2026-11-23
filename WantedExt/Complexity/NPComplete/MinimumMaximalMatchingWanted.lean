/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM MAXIMAL MATCHING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT10] MINIMUM MAXIMAL
MATCHING;
M. Yannakakis and F. Gavril, "Edge dominating sets in graphs", SIAM Journal on
Applied Mathematics 38 (1980), 364-372, doi:10.1137/0138030.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Matching

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumMaximalMatching

/-!
# MINIMUM MAXIMAL MATCHING is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |E|`. QUESTION: is there a subset
`E' ⊆ E` with `|E'| ≤ K` such that `E'` is a maximal matching, that is, no two edges of `E'`
share a common endpoint and every edge in `E - E'` shares a common endpoint with some edge
of `E'`?

The matching `E'` is a Mathlib subgraph `M` of `G` with `M.IsMatching`; its edge set is
`M.edgeSet ⊆ E`. Under `WellFormed` the edge list has one entry per edge, so its length is
`|E|`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev MinimumMaximalMatchingInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MinimumMaximalMatchingInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and
`0 < K ≤ |E|`, the length of the edge list. -/
def WellFormed (i : MinimumMaximalMatchingInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- A maximal matching of at most `K` edges: a matching `M` of the graph with at most `K`
edges such that every edge `{u, v}` of the graph that is not in `M` shares an endpoint with
an edge of `M`. -/
def MinimumMaximalMatchingFeasible (i : MinimumMaximalMatchingInstance) : Prop :=
  ∃ M : (Graph i).Subgraph, M.IsMatching ∧ M.edgeSet.ncard ≤ i.2.2 ∧
    ∀ u v, (Graph i).Adj u v → ¬ M.Adj u v → ∃ w, M.Adj u w ∨ M.Adj v w

open Classical in
/-- MINIMUM MAXIMAL MATCHING as a decision problem over bitstrings. -/
noncomputable def minimumMaximalMatchingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumMaximalMatchingInstance) x with
  | some i => decide (WellFormed i ∧ MinimumMaximalMatchingFeasible i)
  | none => false

/-- **MINIMUM MAXIMAL MATCHING is NP-complete.** Source: Garey and Johnson (1979), [GT10];
Yannakakis and Gavril (1980). -/
public theorem_wanted minimumMaximalMatching_npComplete :
    minimumMaximalMatchingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumMaximalMatchingDec

end MetaMathlibExt.Complexity.NPComplete.MinimumMaximalMatching
