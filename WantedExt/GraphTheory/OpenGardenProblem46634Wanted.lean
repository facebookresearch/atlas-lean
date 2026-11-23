/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Source record `OPG-46634`
# Large induced forests in planar graphs

Open Problem Garden, node 46634 (Albertson–Berman conjecture).

Planarity is the shared straight-line planarity predicate `SimpleGraph.IsPlanar` of `MathlibExt`
(a crossing-free straight-line drawing; by Fáry's theorem this is planarity for finite simple
graphs). An induced forest is a vertex set whose induced subgraph is acyclic.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Fintype.Card
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.GraphTheory.OpenGardenProblem46634Wanted

/-- The Albertson–Berman conjecture: every planar graph on `n` vertices has an induced forest with
at least `n / 2` vertices. -/
def conjecture : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.IsPlanar →
    ∃ S : Finset V, (G.induce (S : Set V)).IsAcyclic ∧ Fintype.card V ≤ 2 * S.card

/--
Resolved false: Resolved false: Open Problem Garden now records counterexamples by H. Jung (an
explicit 31-vertex plane triangulation T with largest induced forest a(T) = 15,
arXiv:2608.17350) and, independently and without AI, M. Makarov (39 vertices, a(G) = 19,
arXiv:2608.13964), plus a smaller one by W. Cames van Batenburg (House of Graphs 57246). Each is
a planar graph with no induced forest on n/2 vertices. Source: H. Jung, A 15/31 counterexample
family to the Albertson-Berman conjecture, arXiv:2608.17350 (2026),
https://arxiv.org/abs/2608.17350; Open Problem Garden, Large induced forest in a planar graph
(node 46634), counterexample note (Jung; Makarov; Cames van Batenburg),
https://www.openproblemgarden.org/op/large_induced_forest_in_a_planar_graph; M. Makarov, A
counterexample to the Albertson-Berman conjecture about induced forests in planar graphs,
arXiv:2608.13964 (2026), https://arxiv.org/abs/2608.13964. Moved from
`OpenConjectures/GraphTheory/OpenGardenProblem46634`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.GraphTheory.OpenGardenProblem46634Wanted
