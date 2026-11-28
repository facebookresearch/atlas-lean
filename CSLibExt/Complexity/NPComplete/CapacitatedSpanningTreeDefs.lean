/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CAPACITATED SPANNING TREE: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND5] CAPACITATED SPANNING TREE;
C. H. Papadimitriou, "The complexity of the capacitated tree problem", Networks 8 (1978),
217-230, doi:10.1002/net.3230080306.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTree

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list (an entry `(u, v, c, l)` is
the edge `{u, v}` with capacity `c` and length `l`), the vertex `v₀`, the requirements `r(v)` of
the vertices in order, and the bound `B`. -/
abbrev CapacitatedSpanningTreeInstance := ℕ × List (ℕ × ℕ × ℕ × ℕ) × ℕ × List ℕ × ℕ

/-- The endpoint pairs of the edge list. -/
def endpoints (i : CapacitatedSpanningTreeInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun e => (e.1, e.2.1)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CapacitatedSpanningTreeInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (endpoints i)

/-- The list entry of an edge `s`: the entry whose endpoints are the endpoints of `s` (unique
under `WellFormed`). -/
def entry (i : CapacitatedSpanningTreeInstance) (s : Sym2 (Fin i.1)) :
    Option (ℕ × ℕ × ℕ × ℕ) :=
  i.2.1.find? fun e => s.map Fin.val = s(e.1, e.2.1)

/-- The capacity `c(e)` of an edge. -/
def capacity (i : CapacitatedSpanningTreeInstance) (s : Sym2 (Fin i.1)) : ℕ :=
  ((entry i s).map fun e => e.2.2.1).getD 0

/-- The length `l(e)` of an edge. -/
def edgeLength (i : CapacitatedSpanningTreeInstance) (s : Sym2 (Fin i.1)) : ℕ :=
  ((entry i s).map fun e => e.2.2.2).getD 0

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), `v₀` is a vertex,
and there is one requirement per vertex. -/
def WellFormed (i : CapacitatedSpanningTreeInstance) : Prop :=
  ((endpoints i).Nodup ∧
    ∀ e ∈ endpoints i, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ endpoints i) ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1.length = i.1

open Classical in
/-- Some spanning tree `T` of `G` has total length at most `B`, and for each edge `e` of `T` the
requirements of the vertices whose path to `v₀` in `T` contains `e` sum to at most `c(e)`. -/
def CapacitatedSpanningTreeFeasible (i : CapacitatedSpanningTreeInstance) : Prop :=
  ∃ hv : i.2.2.1 < i.1, ∃ T : SimpleGraph (Fin i.1), T ≤ Graph i ∧ T.IsTree ∧
    ∑ e ∈ T.edgeFinset, edgeLength i e ≤ i.2.2.2.2 ∧
    ∀ e ∈ T.edgeSet,
      ∑ u ∈ Finset.univ.filter (fun u => ∃ p : T.Walk u ⟨i.2.2.1, hv⟩, p.IsPath ∧ e ∈ p.edges),
        i.2.2.2.1.getD u 0 ≤ capacity i e

open Classical in
/-- CAPACITATED SPANNING TREE as a decision problem over bitstrings. -/
noncomputable def capacitatedSpanningTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CapacitatedSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ CapacitatedSpanningTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTree
