/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM t-SPANNER (fixed t ≥ 2): definitions

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

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumTSpanner

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

end MetaMathlibExt.Complexity.NPComplete.MinimumTSpanner
