/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHORDAL EDGE DELETION is NP-complete

Source:
A. Natanzon, R. Shamir and R. Sharan, "Complexity classification of some edge modification
problems", Discrete Applied Mathematics 113 (2001), 109-128,
doi:10.1016/S0166-218X(00)00391-7, Theorem 3.6.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Data.Set.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChordalEdgeDeletion

/-!
# CHORDAL EDGE DELETION is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected) and a nonnegative integer `K`.
QUESTION: can `G` be made chordal by deleting at most `K` edges, i.e., is there a set `F ⊆ E`
with `|F| ≤ K` such that `(V, E \ F)` is chordal?

Natanzon, Shamir and Sharan call a graph chordal if it contains no induced cycle of length
greater than `3`, and prove CHORDAL DELETION NP-complete (Theorem 3.6). The graph after the
deletion is a `SimpleGraph` `H` on the same vertices with `H ≤ G`; the deleted edges are
`G.edgeSet \ H.edgeSet`, as in `ClusterDeletionWanted`. Chordality is stated as in
`DominatingSetChordalGraphsWanted` and `HamiltonianCircuitChordalGraphsWanted`: no cycle graph
`Cₖ` with `k ≥ 4` is an induced subgraph (Mathlib's `SimpleGraph.cycleGraph` and
`SimpleGraph.IsIndContained`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, and the bound `K`. -/
abbrev ChordalEdgeDeletionInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : ChordalEdgeDeletionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph (no duplicate edges
in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : ChordalEdgeDeletionInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- Deleting at most `K` edges of `G` leaves a chordal graph (no induced cycle of length at
least `4`). -/
def ChordalEdgeDeletionFeasible (i : ChordalEdgeDeletionInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), H ≤ Graph i ∧
    ((Graph i).edgeSet \ H.edgeSet).ncard ≤ i.2.2 ∧
      ∀ k, 4 ≤ k → ¬ (SimpleGraph.cycleGraph k).IsIndContained H

open Classical in
/-- CHORDAL EDGE DELETION as a decision problem over bitstrings. -/
noncomputable def chordalEdgeDeletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChordalEdgeDeletionInstance) x with
  | some i => decide (WellFormed i ∧ ChordalEdgeDeletionFeasible i)
  | none => false

/-- **CHORDAL EDGE DELETION is NP-complete.** Source: Natanzon, Shamir and Sharan (2001),
Theorem 3.6. -/
public theorem_wanted chordalEdgeDeletion_npComplete :
    chordalEdgeDeletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chordalEdgeDeletionDec

end MetaMathlibExt.Complexity.NPComplete.ChordalEdgeDeletion
