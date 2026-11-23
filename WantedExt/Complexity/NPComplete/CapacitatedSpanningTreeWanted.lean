/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CAPACITATED SPANNING TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND5] CAPACITATED SPANNING TREE;
C. H. Papadimitriou, "The complexity of the capacitated tree problem", Networks 8 (1978),
217-230, doi:10.1002/net.3230080306.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTree

/-!
# CAPACITATED SPANNING TREE is NP-complete

INSTANCE: a graph `G = (V, E)`, a specified vertex `v₀ ∈ V`, a capacity `c(e) ∈ ℤ₀⁺` and a
length `l(e) ∈ ℤ₀⁺` for each `e ∈ E`, a requirement `r(v) ∈ ℤ₀⁺` for each `v ∈ V - {v₀}`, and a
bound `B ∈ ℤ₀⁺`. QUESTION: is there a spanning tree `T` for `G` such that the sum of the lengths
of the edges in `T` does not exceed `B` and such that for each edge `e` in `T`, if `U(e)` is the
set of vertices whose path to `v₀` in `T` contains `e`, then `∑_{u ∈ U(e)} r(u) ≤ c(e)`?

A spanning tree of `G` is a Mathlib `SimpleGraph` `T` on the vertices of `G` with `T ≤ G` and
`T.IsTree`, the form of Mathlib's `SimpleGraph.Connected.exists_isTree_le`. The path from `u`
to `v₀` in `T` is a `SimpleGraph.Walk` with `SimpleGraph.Walk.IsPath`; it is unique in a tree,
so `u ∈ U(e)` is stated as "some path from `u` to `v₀` in `T` contains `e`". The requirement
list has one entry per vertex; the entry of `v₀` is never read, since `v₀ ∉ U(e)` (its path to
itself has no edges).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **CAPACITATED SPANNING TREE is NP-complete.** Source: Garey and Johnson (1979), [ND5];
Papadimitriou (1978). -/
public theorem_wanted capacitatedSpanningTree_npComplete :
    capacitatedSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L capacitatedSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTree
