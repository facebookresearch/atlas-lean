/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM CUT LINEAR ARRANGEMENT on edge-weighted trees is NP-complete

Source:
B. Monien and I. H. Sudborough, "Min cut is NP-complete for edge weighted trees", Theoretical
Computer Science 58(1-3) (1988), 209-229, doi:10.1016/0304-3975(88)90028-X;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT44] MINIMUM CUT LINEAR ARRANGEMENT.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementWeightedTrees

/-!
# MINIMUM CUT LINEAR ARRANGEMENT on edge-weighted trees is NP-complete

INSTANCE: a tree `T = (V, E)`, edge weights `w : E → ℤ⁺`, and a positive integer `K`.
QUESTION: is there a one-to-one function `f : V → {1, 2, …, |V|}` such that for every `i`, the
total weight of the edges `{u, v}` with `f(u) ≤ i < f(v)` is at most `K`?

This is [GT44] MINIMUM CUT LINEAR ARRANGEMENT (stated without weights in
`WantedExt.Complexity.NPComplete.MinimumCutLinearArrangementWanted`) on trees, with each edge
counted with its weight. Vertices are `0, …, n - 1` and the tree is given by a list of weighted
edges, its graph being `Cslib.Complexity.Karp.edgeGraph` and treeness Mathlib's
`SimpleGraph.IsTree` (connected and acyclic). The numbering `f` is given, as in
`MinimumCutLinearArrangementWanted`, by the positions in a permutation of `0, …, n - 1`.
Monien and Sudborough prove NP-completeness even when the weights are bounded by a polynomial in
`|V|`, so the problem is NP-complete in the strong sense; weights use the canonical binary
encoding. For unweighted trees (all weights `1`) the problem is solvable in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of vertices, the weighted edges `((u, v), w(uv))`, and the
bound `K`. -/
abbrev MinimumCutLinearArrangementWeightedTreesInstance := ℕ × List ((ℕ × ℕ) × ℕ) × ℕ

/-- The tree of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MinimumCutLinearArrangementWeightedTreesInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (i.2.1.map Prod.fst)

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1`
(no duplicate edges in either orientation, no self-loops, endpoints in range) that is a tree,
every weight is positive, and `0 < K`. -/
def WellFormed (i : MinimumCutLinearArrangementWeightedTreesInstance) : Prop :=
  ((i.2.1.map Prod.fst).Nodup ∧ ∀ e ∈ i.2.1.map Prod.fst,
      e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1.map Prod.fst) ∧
    (Graph i).IsTree ∧ (∀ e ∈ i.2.1, 0 < e.2) ∧ 0 < i.2.2

/-- A one-to-one numbering of the vertices, given by the positions in a permutation `perm` of
`0, …, n - 1`, such that for every cut position `j` with `j + 1 < n` the entries of the edge
list with one endpoint at a position `≤ j` and the other at a position `> j` have total weight
at most `K`. Every such entry is summed, so on a list that is not simple an edge can count more
than once. -/
def MinimumCutLinearArrangementWeightedTreesFeasible
    (i : MinimumCutLinearArrangementWeightedTreesInstance) : Prop :=
  ∃ perm : List ℕ, perm.Perm (List.range i.1) ∧
    ∀ j, j + 1 < i.1 →
      ((i.2.1.filter fun e => (perm.idxOf e.1.1 ≤ j ∧ j < perm.idxOf e.1.2) ∨
        (perm.idxOf e.1.2 ≤ j ∧ j < perm.idxOf e.1.1)).map Prod.snd).sum ≤ i.2.2

open Classical in
/-- MINIMUM CUT LINEAR ARRANGEMENT on edge-weighted trees as a decision problem over
bitstrings. -/
noncomputable def minimumCutLinearArrangementWeightedTreesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumCutLinearArrangementWeightedTreesInstance) x with
  | some i => decide (WellFormed i ∧ MinimumCutLinearArrangementWeightedTreesFeasible i)
  | none => false

/-- **MINIMUM CUT LINEAR ARRANGEMENT on edge-weighted trees is NP-complete.** Source: Monien and
Sudborough (1988). -/
public theorem_wanted minimumCutLinearArrangementWeightedTrees_npComplete :
    minimumCutLinearArrangementWeightedTreesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumCutLinearArrangementWeightedTreesDec

end MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementWeightedTrees
