/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM t-SPANNER (fixed t ≥ 2) is NP-complete

Source:
D. Peleg and A. A. Schäffer, "Graph spanners", Journal of Graph Theory 13(1) (1989), 99-116,
doi:10.1002/jgt.3190130114 (`t = 2`);
L. Cai, "NP-completeness of minimum spanner problems", Discrete Applied Mathematics 48(2)
(1994), 187-194, doi:10.1016/0166-218X(94)90073-6 (every fixed `t ≥ 2`);
both restated in R. Ahmed, G. Bodwin, F. Darabi Sahneh, K. Hamm, M. J. Latifi Jebelli,
S. Kobourov and R. Spence, "Graph spanners: A tutorial review", Computer Science Review 37
(2020), 100253, doi:10.1016/j.cosrev.2020.100253 (arXiv:1909.03152), Section 3.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumTSpanner

/-!
# MINIMUM t-SPANNER (fixed t ≥ 2) is NP-complete

Fix an integer `t ≥ 2`. INSTANCE: a connected graph `G = (V, E)` and a positive integer `K`.
QUESTION: does `G` have a `t`-spanner with at most `K` edges, i.e. a subgraph `G' = (V, E')`,
`E' ⊆ E`, with `|E'| ≤ K` and `d_{G'}(u, v) ≤ t · d_G(u, v)` for all `u, v ∈ V`?

Peleg and Schäffer (1989) introduced `t`-spanners and proved this problem NP-complete for
`t = 2`; Cai (1994) proved it NP-complete for every fixed `t ≥ 2`. In the words of the survey of
Ahmed et al. (2020), Section 3.1: Peleg and Schäffer "show that, given an unweighted graph `G`,
and integers `t, m₀ ≥ 1`, determining if `G` has a `t`-spanner containing `m₀` or fewer edges
is NP-complete, even when `t` is fixed to be 2", and "Cai also shows that for any fixed `t ≥ 2`,
the minimum `t`-spanner problem is NP-hard"; the survey's Problem 1 defines a `t`-spanner of a
connected graph `G = (V, E)` as a subgraph `G' = (V, E')`, `E' ⊆ E`, with
`d_{G'}(u, v) ≤ t · d_G(u, v)` for all `u, v ∈ V`. Membership in NP holds because a spanner is
a certificate checked by breadth-first search.

`t` is fixed, not part of the instance: the decision problem is `minimumTSpannerDec t`, and the
theorem holds for every `t ≥ 2`. The graph is given by an edge list on `Fin n`. A subgraph on
the same vertex set is a `SimpleGraph (Fin n)` below `G` (`H ≤ G`), its number of edges is
`H.edgeSet.ncard`, and distances are Mathlib's extended distance `SimpleGraph.edist` (in
`ℕ∞`, `⊤` between vertices in different components), so a pair connected in `G` but not in `H`
violates the inequality.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, and the bound `K`. -/
abbrev MinimumTSpannerInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MinimumTSpannerInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph (no duplicate
edges in either orientation, no self-loops, endpoints in range), the graph is connected, and
`K` is positive. -/
def WellFormed (i : MinimumTSpannerInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).Connected ∧ 0 < i.2.2

/-- `G` has a `t`-spanner with at most `K` edges: a subgraph `H ≤ G` on the same vertices with
at most `K` edges and `d_H(u, v) ≤ t · d_G(u, v)` for all `u, v`. -/
def MinimumTSpannerFeasible (t : ℕ) (i : MinimumTSpannerInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), H ≤ Graph i ∧ H.edgeSet.ncard ≤ i.2.2 ∧
    ∀ u v, H.edist u v ≤ (t : ℕ∞) * (Graph i).edist u v

open Classical in
/-- MINIMUM `t`-SPANNER, for the fixed `t`, as a decision problem over bitstrings. -/
noncomputable def minimumTSpannerDec (t : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumTSpannerInstance) x with
  | some i => decide (WellFormed i ∧ MinimumTSpannerFeasible t i)
  | none => false

/-- **MINIMUM t-SPANNER is NP-complete for every fixed `t ≥ 2`.** Source: Peleg and Schäffer
(1989) for `t = 2`; Cai (1994) for every fixed `t ≥ 2`; Ahmed et al. (2020), Section 3.1. -/
public theorem_wanted minimumTSpanner_npComplete (t : ℕ) (_ht : 2 ≤ t) :
    minimumTSpannerDec t ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (minimumTSpannerDec t)

end MetaMathlibExt.Complexity.NPComplete.MinimumTSpanner
