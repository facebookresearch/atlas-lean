/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ORIENTED DIAMETER: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT64] ORIENTED
DIAMETER;
V. Chvátal and C. Thomassen, "Distances in orientations of graphs", Journal of
Combinatorial Theory, Series B 24 (1978), 61-75,
doi:10.1016/0095-8956(78)90078-3 (NP-complete already for `K = 2`).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.Digraph.Basic
public import MathlibExt.Combinatorics.SimpleGraph.Dichromatic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OrientedDiameter

/-- `v` is reachable from `u` along at most `K` arcs of `D`: there is a sequence
`p 0 = u, ..., p K = v` in which each step `p t → p (t + 1)` stays put or is an arc of `D`. -/
def ReachWithin {n : ℕ} (D : Digraph (Fin n)) (K : ℕ) (u v : Fin n) : Prop :=
  ∃ p : Fin (K + 1) → Fin n, p 0 = u ∧ p (Fin.last K) = v ∧
    ∀ t : Fin K, p t.castSucc = p t.succ ∨ D.Adj (p t.castSucc) (p t.succ)

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev OrientedDiameterInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : OrientedDiameterInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K ≤ |V|`. -/
def WellFormed (i : OrientedDiameterInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some orientation of the graph has diameter at most `K`: every vertex is reachable from
every vertex along at most `K` arcs (hence the orientation is strongly connected). -/
def OrientedDiameterFeasible (i : OrientedDiameterInstance) : Prop :=
  ∃ D : Digraph (Fin i.1), (Graph i).IsOrientation D.Adj ∧ ∀ u v, ReachWithin D i.2.2 u v

open Classical in
/-- ORIENTED DIAMETER as a decision problem over bitstrings. -/
noncomputable def orientedDiameterDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OrientedDiameterInstance) x with
  | some i => decide (WellFormed i ∧ OrientedDiameterFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OrientedDiameter
