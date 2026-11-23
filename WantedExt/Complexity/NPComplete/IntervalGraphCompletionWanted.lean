/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERVAL GRAPH COMPLETION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT35] INTERVAL GRAPH
COMPLETION (credited there to unpublished work of Garey, Gavril, and Johnson);
K. Yamaguchi, T. Araki, and T. Kashiwabara, "NP-completeness of interval graph
completion from a path graph", Electronics and Communications in Japan, Part III
78(6) (1995), 95-102, doi:10.1002/ecjc.4430780610 (NP-complete already when the
input graph is a path graph);
Y. Villanger, P. Heggernes, C. Paul, and J. A. Telle, "Interval completion is
fixed parameter tractable", SIAM Journal on Computing 38(5) (2009), 2007-2020,
doi:10.1137/070710913 (records the problem as NP-complete, citing [GT35]).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntervalGraphCompletion

/-!
# INTERVAL GRAPH COMPLETION is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K`. QUESTION: is there a superset `E'`
containing `E` such that `|E' - E| ≤ K` and the graph `G' = (V, E')` is an interval graph?

An interval graph is the intersection graph of a family of intervals on the real line: each
vertex `v` is assigned a closed interval `[l v, r v]` (`l v ≤ r v`), and two distinct vertices are
adjacent exactly when their intervals intersect (`IsIntervalGraph`). The supergraph `G'` is a
`SimpleGraph` `H` on the same vertices with `G ≤ H`, and `|E' - E|` is the number of edges of
`H` that are not edges of `G` (`Set.ncard` of the difference of the edge sets).

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
abbrev IntervalGraphCompletionInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IntervalGraphCompletionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K`. -/
def WellFormed (i : IntervalGraphCompletionInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- `H` is an interval graph: there are closed real intervals `[l v, r v]`, one per vertex, such
that two distinct vertices are adjacent in `H` exactly when their intervals intersect. -/
def IsIntervalGraph {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ∃ l r : Fin n → ℝ, (∀ v, l v ≤ r v) ∧
    ∀ u v, u ≠ v → (H.Adj u v ↔ (Set.Icc (l u) (r u) ∩ Set.Icc (l v) (r v)).Nonempty)

/-- Some interval graph `H` on the same vertices contains the graph and has at most `K` edges
that are not edges of the graph. -/
def IntervalGraphCompletionFeasible (i : IntervalGraphCompletionInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), Graph i ≤ H ∧
    (H.edgeSet \ (Graph i).edgeSet).ncard ≤ i.2.2 ∧ IsIntervalGraph H

open Classical in
/-- INTERVAL GRAPH COMPLETION as a decision problem over bitstrings. -/
noncomputable def intervalGraphCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntervalGraphCompletionInstance) x with
  | some i => decide (WellFormed i ∧ IntervalGraphCompletionFeasible i)
  | none => false

/-- **INTERVAL GRAPH COMPLETION is NP-complete.** Source: Garey and Johnson (1979), [GT35];
Yamaguchi, Araki, and Kashiwabara (1995); Villanger, Heggernes, Paul, and Telle (2009). -/
public theorem_wanted intervalGraphCompletion_npComplete :
    intervalGraphCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L intervalGraphCompletionDec

end MetaMathlibExt.Complexity.NPComplete.IntervalGraphCompletion
