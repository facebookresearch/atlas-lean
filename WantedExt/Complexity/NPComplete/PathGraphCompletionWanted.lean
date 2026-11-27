/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH GRAPH COMPLETION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT36] PATH GRAPH COMPLETION, p. 199
(reference: [Gavril, 1977b], listed in Garey and Johnson's bibliography as F. Gavril, private
communication; transformation from INTERVAL GRAPH COMPLETION). The original was not available;
Garey and Johnson's entry records the result and its attribution.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Data.Set.Card
public import WantedExt.Complexity.NPComplete.DominatingSetUndirectedPathGraphsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathGraphCompletion

/-!
# PATH GRAPH COMPLETION is NP-complete

INSTANCE: a graph `G = (V, E)` and a non-negative integer `K`.
QUESTION: is there a superset `E'` containing `E` such that `|E' - E| ≤ K` and the graph
`G' = (V, E')` is the intersection graph of a family of paths on an undirected tree?

The intersection graph of a family of paths on an undirected tree (an undirected path graph) is
the repository's `DominatingSetUndirectedPathGraphs.IsUndirectedPathGraph`: for some finite tree
`T` (Mathlib's `SimpleGraph.IsTree`) on `Fin m`, every vertex `v` has the vertex set `P v` of a
path of `T` (a `SimpleGraph.Walk` with `IsPath`, possibly a single tree vertex), and two distinct
vertices are adjacent exactly when their paths share a tree vertex. The variant with directed
paths on a rooted tree, from Garey and Johnson's comment, is
`RootedDirectedPathGraphCompletionWanted`.

As in `IntervalGraphCompletionWanted`, the supergraph `G'` is a `SimpleGraph` `H` on the same
vertices with `G ≤ H`, and `|E' - E|` is the number of edges of `H` that are not edges of `G`
(`Set.ncard` of the difference of the edge sets).

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
abbrev PathGraphCompletionInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PathGraphCompletionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range); `K ≥ 0` needs no
condition. -/
def WellFormed (i : PathGraphCompletionInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- Some undirected path graph `H` on the same vertices contains the graph and has at most `K`
edges that are not edges of the graph. -/
def PathGraphCompletionFeasible (i : PathGraphCompletionInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), Graph i ≤ H ∧
    (H.edgeSet \ (Graph i).edgeSet).ncard ≤ i.2.2 ∧
      DominatingSetUndirectedPathGraphs.IsUndirectedPathGraph H

open Classical in
/-- PATH GRAPH COMPLETION as a decision problem over bitstrings. -/
noncomputable def pathGraphCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathGraphCompletionInstance) x with
  | some i => decide (WellFormed i ∧ PathGraphCompletionFeasible i)
  | none => false

/-- **PATH GRAPH COMPLETION is NP-complete.** Source: Garey and Johnson (1979), [GT36],
citing Gavril (1977b, private communication). -/
public theorem_wanted pathGraphCompletion_npComplete :
    pathGraphCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathGraphCompletionDec

end MetaMathlibExt.Complexity.NPComplete.PathGraphCompletion
