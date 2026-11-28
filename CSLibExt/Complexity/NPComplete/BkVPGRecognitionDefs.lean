/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF B_k-VPG graphs (fixed k): definitions

Source:
S. Chaplick, V. Jelínek, J. Kratochvíl and T. Vyskočil, "Bend-bounded path intersection graphs:
sausages, noodles, and waffles on a grill", WG 2012, Lecture Notes in Computer Science 7551
(2012), 274-285, doi:10.1007/978-3-642-34611-8_28.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BkVPGRecognition

/-- An instance: the vertex count `n` (vertices `0, …, n - 1`) and the edge list. -/
abbrev BkVPGInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : BkVPGInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Two grid points are neighbours on the grid: they differ by `1` in exactly one coordinate. -/
def GridAdj (p q : ℕ × ℕ) : Prop :=
  (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨ (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))

/-- A path on the grid: a nonempty list of distinct grid points, consecutive points neighbours. -/
def IsGridPath (P : List (ℕ × ℕ)) : Prop :=
  P ≠ [] ∧ P.Nodup ∧ P.IsChain GridAdj

/-- The number of bends of a grid path: inner points `b` (with predecessor `a` and successor
`c`) where a horizontal step meets a vertical one. -/
def bends (P : List (ℕ × ℕ)) : ℕ :=
  ((P.zip P.tail).zip P.tail.tail).countP fun t =>
    decide ((t.1.1.2 = t.1.2.2 ∧ t.1.2.2 ≠ t.2.2) ∨ (t.1.1.2 ≠ t.1.2.2 ∧ t.1.2.2 = t.2.2))

/-- `G` is a `B_k`-VPG graph: there are grid paths with at most `k` bends, one per vertex, such
that two distinct vertices are adjacent exactly when their paths share a grid point. -/
def IsBkVPG (k : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ P : Fin n → List (ℕ × ℕ), (∀ v, IsGridPath (P v) ∧ bends (P v) ≤ k) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ ∃ p, p ∈ P u ∧ p ∈ P v)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : BkVPGInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

open Classical in
/-- RECOGNITION OF `B_k`-VPG graphs, for the fixed `k`, as a decision problem over bitstrings. -/
noncomputable def bkVPGRecognitionDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BkVPGInstance) x with
  | some i => decide (WellFormed i ∧ IsBkVPG k (Graph i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BkVPGRecognition
