/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THRESHOLD NUMBER: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT63] THRESHOLD
NUMBER;
V. Chvátal and P. L. Hammer, "Aggregation of inequalities in integer
programming", Annals of Discrete Mathematics 1 (1977), 145-162,
doi:10.1016/S0167-5060(08)70731-3 (threshold graphs and the threshold number);
M. Yannakakis, "The complexity of the partial order dimension problem", SIAM
Journal on Algebraic and Discrete Methods 3 (1982), 351-358,
doi:10.1137/0603036 (NP-complete for every fixed `K ≥ 3`).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Real.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThresholdNumber

/-- A threshold graph (Chvátal and Hammer): there are real weights `a v` and a bound `b` such
that a vertex set `S` is a clique exactly when `∑ v ∈ S, a v ≤ b`. -/
def IsThresholdGraph {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ S : Finset (Fin n),
    H.IsClique (S : Set (Fin n)) ↔ ∑ v ∈ S, a v ≤ b

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev ThresholdNumberInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : ThresholdNumberInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and
`0 < K ≤ |E|`, the length of the edge list. -/
def WellFormed (i : ThresholdNumberInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- The edges split into at most `K` threshold graphs: for some `k ≤ K` there are spanning
subgraphs `H j ≤ G`, `j : Fin k`, each a threshold graph, whose edges together are all edges
of `G`. -/
def ThresholdNumberFeasible (i : ThresholdNumberInstance) : Prop :=
  ∃ k ≤ i.2.2, ∃ H : Fin k → SimpleGraph (Fin i.1),
    (∀ j, H j ≤ Graph i) ∧ (∀ u v, (Graph i).Adj u v → ∃ j, (H j).Adj u v) ∧
      ∀ j, IsThresholdGraph (H j)

open Classical in
/-- THRESHOLD NUMBER as a decision problem over bitstrings. -/
noncomputable def thresholdNumberDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThresholdNumberInstance) x with
  | some i => decide (WellFormed i ∧ ThresholdNumberFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThresholdNumber
