/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROOTED DIRECTED PATH GRAPH COMPLETION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT36] PATH GRAPH COMPLETION, p. 199
(comment: "Corresponding problem in which G' must be the intersection graph of a family of
directed paths on an oriented tree (i.e., rooted, with all arcs directed away from the root) is
also NP-complete"; reference: F. Gavril, 1977b).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RootedDirectedPathGraphCompletion

/-!
# ROOTED DIRECTED PATH GRAPH COMPLETION is NP-complete

INSTANCE: a graph `G = (V, E)` and a non-negative integer `K`.
QUESTION: is there a superset `E'` containing `E` such that `|E' - E| ≤ K` and the graph
`G' = (V, E')` is the intersection graph of a family of directed paths on an oriented tree,
i.e. a rooted tree with all arcs directed away from the root?

This is the variant of PATH GRAPH COMPLETION ([GT36]) in Garey and Johnson's comment, where the
completed graph must be a rooted directed path graph. A rooted directed path graph
(`IsRootedDirectedPathGraph`) has a finite tree `T` (Mathlib's `SimpleGraph.IsTree`) on `Fin m`
with a root `r`, and for every vertex `v` the vertex set `P v` of a path of `T` all of whose
edges point away from the root (each step goes from a tree vertex to one farther from `r`, in
Mathlib's `SimpleGraph.dist`), such that two distinct vertices are adjacent exactly when their
paths share a tree vertex. A path may consist of a single tree vertex. This is
`HamiltonianCircuitDirectedPathGraphsWanted.IsDirectedPathGraph` with the orientation of the
tree fixed by a root, as Garey and Johnson require, instead of arbitrary.

As in `IntervalGraphCompletionWanted`, the supergraph `G'` is a `SimpleGraph` `H` on the same
vertices with `G ≤ H`, and `|E' - E|` is the number of edges of `H` that are not edges of `G`.

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
abbrev RootedDirectedPathGraphCompletionInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : RootedDirectedPathGraphCompletionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range); `K ≥ 0` needs no
condition. -/
def WellFormed (i : RootedDirectedPathGraphCompletionInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- `H` is a rooted directed path graph: for some tree `T` on `Fin m` with root `r`, each vertex
`v` of `H` has the vertex set `P v` of a path of `T` whose every step moves away from `r`, and
distinct vertices are adjacent in `H` exactly when their paths share a vertex. -/
def IsRootedDirectedPathGraph {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ∃ (m : ℕ) (T : SimpleGraph (Fin m)) (r : Fin m), T.IsTree ∧
    ∃ P : Fin n → Finset (Fin m),
      (∀ v, ∃ (a b : Fin m) (p : T.Walk a b), p.IsPath ∧
        (∀ d ∈ p.darts, T.dist r d.fst < T.dist r d.snd) ∧ p.support.toFinset = P v) ∧
      ∀ u v, u ≠ v → (H.Adj u v ↔ (P u ∩ P v).Nonempty)

/-- Some rooted directed path graph `H` on the same vertices contains the graph and has at
most `K` edges that are not edges of the graph. -/
def RootedDirectedPathGraphCompletionFeasible
    (i : RootedDirectedPathGraphCompletionInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), Graph i ≤ H ∧
    (H.edgeSet \ (Graph i).edgeSet).ncard ≤ i.2.2 ∧ IsRootedDirectedPathGraph H

open Classical in
/-- ROOTED DIRECTED PATH GRAPH COMPLETION as a decision problem over bitstrings. -/
noncomputable def rootedDirectedPathGraphCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RootedDirectedPathGraphCompletionInstance) x with
  | some i => decide (WellFormed i ∧ RootedDirectedPathGraphCompletionFeasible i)
  | none => false

/-- **ROOTED DIRECTED PATH GRAPH COMPLETION is NP-complete.** Source: Garey and Johnson
(1979), [GT36], comment (Gavril, 1977b). -/
public theorem_wanted rootedDirectedPathGraphCompletion_npComplete :
    rootedDirectedPathGraphCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rootedDirectedPathGraphCompletionDec

end MetaMathlibExt.Complexity.NPComplete.RootedDirectedPathGraphCompletion
