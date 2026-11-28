/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREE t-SPANNER (fixed t ≥ 4): definitions

Source:
L. Cai and D. G. Corneil, "Tree spanners", SIAM Journal on Discrete Mathematics 8 (1995),
359-387, doi:10.1137/S0895480192237403;
I. Papoutsakis, "Tree spanners of bounded degree graphs", arXiv:1503.06822 (Section 1: the
attribution of NP-completeness for each `t ≥ 4` to Cai and Corneil, and Definition 1 of a tree
`t`-spanner used below).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreeTSpanner

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev TreeTSpannerInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : TreeTSpannerInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : TreeTSpannerInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `G` has a tree `t`-spanner: a spanning tree `T` of `G` (a tree `T ≤ G` on all vertices of
`G`) with `d_T(u, v) ≤ t · d_G(u, v)` for all `u, v`. -/
def TreeTSpannerFeasible (t : ℕ) (i : TreeTSpannerInstance) : Prop :=
  ∃ T : SimpleGraph (Fin i.1), T ≤ Graph i ∧ T.IsTree ∧
    ∀ u v, T.edist u v ≤ (t : ℕ∞) * (Graph i).edist u v

open Classical in
/-- TREE `t`-SPANNER, for the fixed `t`, as a decision problem over bitstrings. -/
noncomputable def treeTSpannerDec (t : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreeTSpannerInstance) x with
  | some i => decide (WellFormed i ∧ TreeTSpannerFeasible t i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TreeTSpanner
