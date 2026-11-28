/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN CHORDAL BIPARTITE GRAPHS: definitions

Source:
H. Müller and A. Brandstädt, "The NP-completeness of Steiner tree and dominating set for chordal
bipartite graphs", Theoretical Computer Science 53 (1987), 257-265,
doi:10.1016/0304-3975(87)90067-3.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SteinerTreeDefs
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Walk.Chord

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeChordalBipartite

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-- `G` is chordal bipartite: bipartite, and every cycle of length at least `6` has a chord
(Mathlib's `Walk.IsChord`: an edge of `G` between two vertices of the cycle that is not an edge of
the cycle). -/
def IsChordalBipartite {V : Type*} (G : SimpleGraph V) : Prop :=
  G.IsBipartite ∧ ∀ (v : V) (c : G.Walk v v), c.IsCycle → 6 ≤ c.length → ∃ e, c.IsChord e

/-- Well-formedness of an instance: it is a well-formed STEINER TREE IN GRAPHS instance, every
edge has weight `1`, its graph is chordal bipartite, it has at least one vertex, and `K` is
positive. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    IsChordalBipartite (SteinerTree.Graph i i.2.1) ∧ 0 < i.1 ∧ 0 < i.2.2.2

/-- The parent instance with edge budget `K - 1` (a tree with at most `K` vertices has at most
`K - 1` edges). -/
def toEdgeBudget (i : SteinerTreeInstance) : SteinerTreeInstance :=
  (i.1, i.2.1, i.2.2.1, i.2.2.2 - 1)

open Classical in
/-- STEINER TREE IN CHORDAL BIPARTITE GRAPHS as a decision problem over bitstrings. -/
noncomputable def steinerTreeChordalBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible (toEdgeBudget i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeChordalBipartite
