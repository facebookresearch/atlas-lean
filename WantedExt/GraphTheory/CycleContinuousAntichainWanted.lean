/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card

@[expose] public section

open scoped BigOperators

namespace MathlibExt.GraphTheory.CycleContinuousAntichainWanted

/-! UnsolvedMath record `OPG-323__3223`. -/


/-- **Multigraphs with loops and parallel edges.** A multigraph $G$ consists of a type $V$ of
vertices, a type $E$ of edges, and a map assigning to each edge an ordered pair of vertices,
its two endpoints. Distinct edges may have the same endpoints (parallel edges), and the two
endpoints of an edge may coincide (a loop). Neither $V$ nor $E$ is required to be finite.

Source: [OPG-323] Antichains in the cycle continuous order
(URL: http://www.openproblemgarden.org/op/antichains_in_the_cycle_continuous_order). -/
structure FGraph where
  V : Type
  E : Type
  ends : E → V × V

/-- **Finite multigraphs with at least one edge.** A multigraph $G$ is finite and nontrivial
when its set of vertices and its set of edges are both finite and it has at least one edge.
These are the graphs on which the cycle-continuous order is considered.

Source: [OPG-323]
(URL: http://www.openproblemgarden.org/op/antichains_in_the_cycle_continuous_order). -/
def IsFiniteNontrivial (G : FGraph) : Prop :=
  Finite G.V ∧ Finite G.E ∧ Nonempty G.E

/-- **Binary cycle space.** Let $G$ be a multigraph. A set $S$ of edges of $G$ is a binary cycle
when $S$ is finite and every vertex $v$ is an endpoint of an even number of edges of $S$, where
only edges with exactly one endpoint equal to $v$ are counted; loops are not counted, which
agrees modulo $2$ with counting each loop twice. The cycle space of $G$ is the set of all
binary cycles of $G$.

Source: [OPG-323]
(URL: http://www.openproblemgarden.org/op/antichains_in_the_cycle_continuous_order). -/
noncomputable def cycleSpace (G : FGraph) : Set (Set G.E) :=
  {S | Set.Finite S ∧ ∀ v : G.V, Even (Set.ncard {e ∈ S | ((G.ends e).1 = v ∧ (G.ends e).2 ≠ v) ∨ ((G.ends e).1 ≠ v ∧ (G.ends e).2 = v)})}

/-- **Cycle-continuous maps.** Let $G$ and $H$ be multigraphs. A map $f$ from the edges of $G$
to the edges of $H$ is cycle-continuous when, for every binary cycle $C$ of $H$, the preimage
$f^{-1}(C)$ is a binary cycle of $G$.

Source: [OPG-323]
(URL: http://www.openproblemgarden.org/op/antichains_in_the_cycle_continuous_order). -/
noncomputable def IsCycleContinuous (G H : FGraph) (f : G.E → H.E) : Prop :=
  ∀ C ∈ cycleSpace H, f ⁻¹' C ∈ cycleSpace G

/-- **Infinite antichains in the cycle-continuous order.** There is a sequence
$G_0, G_1, G_2, \dots$ of pairwise distinct finite multigraphs, each with at least one edge,
such that for all $i \ne j$ there is no cycle-continuous map from the edges of $G_i$ to the
edges of $G_j$.

Source: [OPG-323]
(URL: http://www.openproblemgarden.org/op/antichains_in_the_cycle_continuous_order). -/
noncomputable def conjecture : Prop :=
  ∃ G : ℕ → FGraph, (∀ n, IsFiniteNontrivial (G n)) ∧ Function.Injective G ∧ ∀ i j, i ≠ j → ¬∃ f : (G i).E → (G j).E, IsCycleContinuous (G i) (G j) f
/-- **Samal's theorem: infinite antichains in the cycle-continuous order exist.** There is a
sequence $G_0, G_1, G_2, \dots$ of pairwise distinct finite multigraphs, each with at least one
edge, such that for all $i \ne j$ there is no cycle-continuous map from the edges of $G_i$ to
the edges of $G_j$.

Samal (Theorem 1.3) proves this with an infinite set of cubic bridgeless graphs that are
pairwise incomparable under cycle-continuous maps, answering the DeVos-Nesetril-Raspaud
antichain question positively.

Source: Robert Samal, Cycle-continuous
mappings - order structure, Journal of Graph Theory 85 (2017) 56-73, arXiv:1212.6909,
https://arxiv.org/abs/1212.6909. Moved from
`OpenConjectures/GraphTheory/CycleContinuousAntichain`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.GraphTheory.CycleContinuousAntichainWanted
