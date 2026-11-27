/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED DIAMETER SPANNING TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND4] BOUNDED DIAMETER
SPANNING TREE, p. 206 (reference: [Garey and Johnson, unpublished], transformation from
EXACT COVER BY 3-SETS).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedDiameterSpanningTree

/-!
# BOUNDED DIAMETER SPANNING TREE is NP-complete

INSTANCE: a graph `G = (V, E)`, a weight `w(e) ∈ ℤ⁺` for each `e ∈ E`, a positive integer
`D ≤ |V|`, and a positive integer `B`. QUESTION: is there a spanning tree `T` for `G` such that
the sum of the weights of the edges in `T` does not exceed `B` and such that `T` contains no
simple path with more than `D` edges?

The vertices are `Fin n` and the graph is given by a simple edge list with weights (an entry
`(u, v, w)` is the edge `{u, v}` of weight `w`). A spanning tree of `G` is a Mathlib
`SimpleGraph` `T` on the vertices of `G` with `T ≤ G` and `T.IsTree`, the form of Mathlib's
`SimpleGraph.Connected.exists_isTree_le`. A simple path in `T` is a `SimpleGraph.Walk` with
`SimpleGraph.Walk.IsPath`, and its number of edges is `SimpleGraph.Walk.length`. Weights are in
binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list (an entry `(u, v, w)` is the
edge `{u, v}` with weight `w`), the bound `D`, and the bound `B`. -/
abbrev BoundedDiameterSpanningTreeInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ

/-- The endpoint pairs of the edge list. -/
def endpoints (i : BoundedDiameterSpanningTreeInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun e => (e.1, e.2.1)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : BoundedDiameterSpanningTreeInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (endpoints i)

/-- The weight `w(e)` of an edge `s`: the weight of the list entry whose endpoints are the
endpoints of `s` (unique under `WellFormed`), and `0` when there is none. -/
def weight (i : BoundedDiameterSpanningTreeInstance) (s : Sym2 (Fin i.1)) : ℕ :=
  ((i.2.1.find? fun e => s.map Fin.val = s(e.1, e.2.1)).map fun e => e.2.2).getD 0

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), every weight is
positive, `0 < D ≤ |V|`, and `0 < B`. -/
def WellFormed (i : BoundedDiameterSpanningTreeInstance) : Prop :=
  ((endpoints i).Nodup ∧
    ∀ e ∈ endpoints i, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ endpoints i) ∧
    (∀ e ∈ i.2.1, 0 < e.2.2) ∧ 0 < i.2.2.1 ∧ i.2.2.1 ≤ i.1 ∧ 0 < i.2.2.2

open Classical in
/-- Some spanning tree `T` of `G` has total weight at most `B` and contains no simple path with
more than `D` edges. -/
def BoundedDiameterSpanningTreeFeasible (i : BoundedDiameterSpanningTreeInstance) : Prop :=
  ∃ T : SimpleGraph (Fin i.1), T ≤ Graph i ∧ T.IsTree ∧
    ∑ e ∈ T.edgeFinset, weight i e ≤ i.2.2.2 ∧
    ∀ (u v : Fin i.1) (p : T.Walk u v), p.IsPath → p.length ≤ i.2.2.1

open Classical in
/-- BOUNDED DIAMETER SPANNING TREE as a decision problem over bitstrings. -/
noncomputable def boundedDiameterSpanningTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BoundedDiameterSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ BoundedDiameterSpanningTreeFeasible i)
  | none => false

/-- **BOUNDED DIAMETER SPANNING TREE is NP-complete.** Source: Garey and Johnson (1979), [ND4]
(attributed there to Garey and Johnson, unpublished). -/
public theorem_wanted boundedDiameterSpanningTree_npComplete :
    boundedDiameterSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L boundedDiameterSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.BoundedDiameterSpanningTree
