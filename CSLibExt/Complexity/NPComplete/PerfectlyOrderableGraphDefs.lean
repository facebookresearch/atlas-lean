/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PERFECTLY ORDERABLE GRAPH RECOGNITION: definitions

Source:
M. Middendorf and F. Pfeiffer, "On the complexity of recognizing perfectly orderable graphs",
Discrete Mathematics 80(3) (1990), 327-333, doi:10.1016/0012-365X(90)90251-C;
V. Chvátal, "Perfectly orderable graphs", in *Topics in Perfect Graphs* (C. Berge and
V. Chvátal, eds.), Annals of Discrete Mathematics 21 (1984), 63-68 (definition and the
obstruction characterization).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PerfectlyOrderableGraph

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev PerfectlyOrderableGraphInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PerfectlyOrderableGraphInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : PerfectlyOrderableGraphInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The vertex order given by the ranks `rank` has no obstruction: no induced path
`a - b - c - d` of `G` has `a` before `b` and `d` before `c`. -/
def IsPerfectOrder {n : ℕ} (G : SimpleGraph (Fin n)) (rank : Fin n → ℕ) : Prop :=
  ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj a c → ¬ G.Adj b d → ¬ G.Adj a d →
    ¬ (rank a < rank b ∧ rank d < rank c)

/-- The graph is perfectly orderable: some linear order of its vertices (distinct ranks) is a
perfect order. -/
def PerfectlyOrderableGraphFeasible (i : PerfectlyOrderableGraphInstance) : Prop :=
  ∃ rank : Fin i.1 → ℕ, Function.Injective rank ∧ IsPerfectOrder (Graph i) rank

open Classical in
/-- PERFECTLY ORDERABLE GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def perfectlyOrderableGraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PerfectlyOrderableGraphInstance) x with
  | some i => decide (WellFormed i ∧ PerfectlyOrderableGraphFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PerfectlyOrderableGraph
