/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIAMETER SPANNING SUBGRAPH: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, web edition
(2000), problem MINIMUM DIAMETER SPANNING SUBGRAPH (decision version);
J. Plesník, "The complexity of designing a network with minimum diameter", Networks 11(1)
(1981), 77-85, doi:10.1002/net.3230110110;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND4] BOUNDED DIAMETER SPANNING TREE (the
spanning-tree analogue).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DiameterSpanningSubgraph

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list (an entry `(u, v, w, l)` is
the edge `{u, v}` with weight `w` and length `l`), the budget `B`, and the bound `K`. -/
abbrev DiameterSpanningSubgraphInstance := ℕ × List (ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ

/-- The endpoint pairs of a list of edges. -/
def endpoints (es : List (ℕ × ℕ × ℕ × ℕ)) : List (ℕ × ℕ) :=
  es.map fun e => (e.1, e.2.1)

/-- The spanning subgraph `(V, E')` on the vertices `Fin n` with edge list `E'`. -/
def spanning (i : DiameterSpanningSubgraphInstance) (E' : List (ℕ × ℕ × ℕ × ℕ)) :
    SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (endpoints E')

/-- The length `l(e)` of an edge `s`: the length of the list entry whose endpoints are the
endpoints of `s` (unique under `WellFormed`), and `0` when there is none. -/
def edgeLength (i : DiameterSpanningSubgraphInstance) (s : Sym2 (Fin i.1)) : ℕ :=
  ((i.2.1.find? fun e => s.map Fin.val = s(e.1, e.2.1)).map fun e => e.2.2.2).getD 0

/-- The length of a walk: the sum of the lengths of the edges it traverses. -/
def walkLength (i : DiameterSpanningSubgraphInstance) {G : SimpleGraph (Fin i.1)}
    {u v : Fin i.1} (p : G.Walk u v) : ℕ :=
  (p.edges.map (edgeLength i)).sum

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), every weight is
positive, and `B` and `K` are positive. -/
def WellFormed (i : DiameterSpanningSubgraphInstance) : Prop :=
  ((endpoints i.2.1).Nodup ∧
    ∀ e ∈ endpoints i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ endpoints i.2.1) ∧
    (∀ e ∈ i.2.1, 0 < e.2.2.1) ∧ 0 < i.2.2.1 ∧ 0 < i.2.2.2

/-- Some set `E'` of edges (a sublist of the edge list) has total weight at most `B`, and in the
spanning subgraph `(V, E')` every two vertices are joined by a walk of length at most `K`. -/
def DiameterSpanningSubgraphFeasible (i : DiameterSpanningSubgraphInstance) : Prop :=
  ∃ E' : List (ℕ × ℕ × ℕ × ℕ), E'.Sublist i.2.1 ∧ (E'.map fun e => e.2.2.1).sum ≤ i.2.2.1 ∧
    ∀ u v : Fin i.1, ∃ p : (spanning i E').Walk u v, walkLength i p ≤ i.2.2.2

open Classical in
/-- DIAMETER SPANNING SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def diameterSpanningSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DiameterSpanningSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ DiameterSpanningSubgraphFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DiameterSpanningSubgraph
