/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM MAXIMAL MATCHING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT10] MINIMUM MAXIMAL
MATCHING;
M. Yannakakis and F. Gavril, "Edge dominating sets in graphs", SIAM Journal on
Applied Mathematics 38 (1980), 364-372, doi:10.1137/0138030.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Matching

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumMaximalMatching

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

end MetaMathlibExt.Complexity.NPComplete.MinimumMaximalMatching
