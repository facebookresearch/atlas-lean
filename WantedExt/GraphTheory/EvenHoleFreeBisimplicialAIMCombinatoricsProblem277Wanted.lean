/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Even-hole-free graphs have bisimplicial vertices (AIM perfect graph conjecture, Conjecture 4)

AIM workshop The perfect graph conjecture, problem list, section Even-hole-free graphs, Conjecture 4
(Hayward and Reed): an even-hole-free graph contains a vertex whose neighbourhood can be partitioned
into two cliques.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.GraphTheory.EvenHoleFreeBisimplicialAIMCombinatoricsProblem277Wanted

/-!
Source: AIM workshop The perfect graph conjecture, problem list,
https://aimath.org/WWN/perfectgraph/perfectgraph.pdf, section G.4 Even-hole-free graphs, Conjecture
4 (Hayward and Reed). UnsolvedMath record UM-20001152 (`AIM-COMBINATORICS-0277`), dataset
ulamai/UnsolvedMath v1.8.0.

Graphs are finite, simple and nonempty (the null graph has no vertex). A hole is an induced cycle of
length at least four; even-hole-free means no induced copy (graph embedding) of `cycleGraph (2k)`
with `k ≥ 2`, written out in the statement. The two cliques are disjoint and may be empty.
-/

/-- The Hayward-Reed conjecture (AIM, The perfect graph conjecture, Conjecture 4): every finite
nonempty even-hole-free graph (no induced copy, i.e. graph embedding, of `cycleGraph (2 k)` with
`k ≥ 2`: no induced even cycle of length at least four) has a vertex whose neighbourhood can be
partitioned into two cliques (a bisimplicial vertex). -/
def evenHoleFreeHasBisimplicialVertex : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
    (∀ k : ℕ, 2 ≤ k → ¬ (SimpleGraph.cycleGraph (2 * k)).IsIndContained G) →
    ∃ v : V, ∃ C₁ C₂ : Set V, G.IsClique C₁ ∧ G.IsClique C₂ ∧ Disjoint C₁ C₂ ∧
      G.neighborSet v = C₁ ∪ C₂

/--
Resolved true: Chudnovsky and Seymour proved (their 1.1) that every non-null even-hole-free graph
has a bisimplicial vertex, a vertex whose neighbourhood is the union of two cliques (equivalently,
can be partitioned into two cliques). This replaces the 2008 proof of Addario-Berry, Chudnovsky,
Havet, Reed and Seymour, which has a serious error. Source: AIM workshop The perfect graph
conjecture, problem list, https://aimath.org/WWN/perfectgraph/perfectgraph.pdf, section G.4
Even-hole-free graphs, Conjecture 4 (Hayward and Reed); resolution: M. Chudnovsky and P. Seymour,
Even-hole-free graphs still have bisimplicial vertices, J. Combin. Theory Ser. B 161 (2023),
331-381, arXiv:1909.10967, statement 1.1: every non-null even-hole-free graph has a bisimplicial
vertex (a vertex whose neighbourhood is the union of two cliques); the earlier proof of
Addario-Berry, Chudnovsky, Havet, Reed and Seymour (J. Combin. Theory Ser. B 98 (2008)) has an error
that this paper replaces, https://doi.org/10.1016/j.jctb.2023.02.009.
-/
public theorem_wanted evenHoleFreeHasBisimplicialVertex_holds : evenHoleFreeHasBisimplicialVertex

end MathlibExt.GraphTheory.EvenHoleFreeBisimplicialAIMCombinatoricsProblem277Wanted
