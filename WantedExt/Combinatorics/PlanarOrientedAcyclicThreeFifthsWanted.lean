/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Large acyclic induced subdigraphs in planar oriented graphs
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Digraph.Orientation
public import Mathlib.Logic.Relation
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MathlibExt.Combinatorics.PlanarOrientedAcyclicThreeFifthsWanted

/-! Source record `OPG-52197`. -/

/-- An oriented graph is loopless and never contains both orientations of one edge. Mathlib's
`Digraph` is relation-valued, so parallel arcs are absent. -/
def IsOriented {V : Type} (D : Digraph V) : Prop :=
  (∀ v : V, ¬ D.Adj v v) ∧
    ∀ u v : V, D.Adj u v → ¬ D.Adj v u

/-- The directed relation induced on a finite vertex subset. -/
def inducedRelation {V : Type} (D : Digraph V) (S : Finset V)
    (u v : V) : Prop :=
  u ∈ S ∧ v ∈ S ∧ D.Adj u v

/-- A finite vertex subset is acyclic when its induced directed relation has no nonempty closed
directed walk, expressed as irreflexivity of transitive closure. -/
def IsAcyclicInduced {V : Type} (D : Digraph V) (S : Finset V) : Prop :=
  ∀ v : V, ¬ Relation.TransGen (inducedRelation D S) v v

/-- Every finite planar oriented graph admits an acyclic induced subdigraph on at least three
fifths of its vertices. The cross-multiplied bound `3 * |V| ≤ 5 * |S|` is the exact
normalization of `|S| ≥ 3 |V| / 5` over the naturals, with no rounding ambiguity. -/
def conjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (D : Digraph V),
    IsOriented D → SimpleGraph.IsPlanar D.toSimpleGraphInclusive →
      ∃ S : Finset V, IsAcyclicInduced D S ∧ 3 * Fintype.card V ≤ 5 * S.card

/--
Resolved false: Knauer, Valicov, and Wenger (arXiv:1504.06726v2) disprove Harutyunyan's 3n/5
conjecture: oriented planar graphs exist whose maximum acyclic set has size at most
ceil((n+1)/2). Source: Kolja Knauer, Petru Valicov, and Paul S. Wenger, Planar digraphs without
large acyclic sets, arXiv:1504.06726v2 (2016), https://arxiv.org/abs/1504.06726v2. Moved from
`OpenConjectures/Combinatorics/PlanarOrientedAcyclicThreeFifths`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.PlanarOrientedAcyclicThreeFifthsWanted
