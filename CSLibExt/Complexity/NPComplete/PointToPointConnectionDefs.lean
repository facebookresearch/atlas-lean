/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POINT-TO-POINT CONNECTION: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, web edition
(2000), section Graph Theory, problem MINIMUM POINT-TO-POINT CONNECTION (decision version);
C.-L. Li, S. T. McCormick and D. Simchi-Levi, "The point-to-point delivery and connection
problems: complexity and algorithms", Discrete Appl. Math. 36 (1992), 267-292,
doi:10.1016/0166-218X(92)90258-C, Section 2 (definition) and Section 3 (all four point-to-point
connection problems are strongly NP-hard).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PointToPointConnection

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), edge list with weights
`(u, v, w(u, v))`, the source-destination pairs `(sⱼ, dⱼ)`, and `K`. -/
abbrev PointToPointConnectionInstance := ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), every source and
destination is a vertex, and `K` is positive. -/
def WellFormed (i : PointToPointConnectionInstance) : Prop :=
  ((i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧
      (e.2.1, e.1) ∉ i.2.1.map fun e => (e.1, e.2.1)) ∧
    (∀ q ∈ i.2.2.1, q.1 < i.1 ∧ q.2 < i.1) ∧ 0 < i.2.2.2

/-- Some sublist `E'` of the edges has total weight at most `K` and connects every pair: in the
graph with edge set `E'`, each destination `dⱼ` is reachable from its source `sⱼ`. -/
def PointToPointConnectionFeasible (i : PointToPointConnectionInstance) : Prop :=
  ∃ E' : List (ℕ × ℕ × ℕ), E'.Sublist i.2.1 ∧ (E'.map fun e => e.2.2).sum ≤ i.2.2.2 ∧
    ∀ q ∈ i.2.2.1, ∀ (hs : q.1 < i.1) (hd : q.2 < i.1),
      (Cslib.Complexity.Karp.edgeGraph i.1 (E'.map fun e => (e.1, e.2.1))).Reachable
        ⟨q.1, hs⟩ ⟨q.2, hd⟩

open Classical in
/-- POINT-TO-POINT CONNECTION as a decision problem over bitstrings. -/
noncomputable def pointToPointConnectionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PointToPointConnectionInstance) x with
  | some i => decide (WellFormed i ∧ PointToPointConnectionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PointToPointConnection
