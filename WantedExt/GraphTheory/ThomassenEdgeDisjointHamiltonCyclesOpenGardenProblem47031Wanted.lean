/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Edge-disjoint Hamilton cycles in highly connected tournaments (Open Problem Garden 47031)

Open Problem Garden, Edge-disjoint Hamilton cycles in highly strongly connected tournaments (C.
Thomassen): for every `k ≥ 2` there is an integer `f(k)` such that every strongly `f(k)`-connected
tournament has `k` edge-disjoint Hamilton cycles.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Order.CompletePartialOrder
public import WantedExt.Combinatorics.TransitiveSubtournamentLogErdosProblem1216Wanted
public import WantedExt.GraphTheory.TournamentStrongConnectivityShared

@[expose] public section

namespace MathlibExt.GraphTheory.ThomassenEdgeDisjointHamiltonCyclesOpenGardenProblem47031Wanted

/-!
Source: Open Problem Garden, Edge-disjoint Hamilton cycles in highly strongly connected tournaments
(node 47031; C. Thomassen), http://www.openproblemgarden.org/op/edge_disjoint_hamilton_cycles.
UnsolvedMath record UM-00003278 (`OPG-47031`), dataset ulamai/UnsolvedMath v1.8.0.

A tournament on `Fin n` is an arc relation as in `IsTournament` (irreflexive, exactly one arc
between distinct vertices). Strongly `k`-connected means more than `k` vertices and strongly
connected after deleting any fewer than `k` vertices (Kühn-Lapinskas-Osthus-Patel, Section 2). A
Hamilton cycle is a cyclic ordering `c` of all vertices with arcs `c i → c (i + 1)`; edge-disjoint
means no common arc. The target is stated for every `k`: `k = 0` is vacuous and `k = 1` is Camion's
theorem (`f(1) = 1`, Kühn-Lapinskas-Osthus-Patel, abstract).
-/

open MathlibExt.Combinatorics.TransitiveSubtournamentLogErdosProblem1216Wanted
open MathlibExt.GraphTheory.TournamentStrongConnectivityShared

/-- The cyclic ordering `c` of the vertices of `Fin n` is a Hamilton cycle of the arc relation `T`:
`c i → c (i + 1)` is an arc for every `i`, indices taken modulo `n`. -/
def IsHamiltonCycle {n : ℕ} (T : Fin n → Fin n → Prop) (c : Equiv.Perm (Fin n)) : Prop :=
  ∀ i, T (c i) (c (finRotate n i))

/-- The arcs `c i → c (i + 1)` (indices modulo `n`) of the cyclic ordering `c`. -/
def cycleArcs {n : ℕ} (c : Equiv.Perm (Fin n)) : Set (Fin n × Fin n) :=
  Set.range fun i => (c i, c (finRotate n i))

/-- Thomassen's conjecture: for every `k` there is `f(k)` such that every strongly
`f(k)`-connected tournament has `k` edge-disjoint Hamilton cycles. -/
def thomassenHamiltonCycles : Prop :=
  ∀ k : ℕ, ∃ f : ℕ, ∀ (n : ℕ) (T : Fin n → Fin n → Prop), IsTournament T →
    IsStronglyKConnectedOn T Finset.univ f →
      ∃ c : Fin k → Equiv.Perm (Fin n), (∀ j, IsHamiltonCycle T (c j)) ∧
        ∀ j j', j ≠ j' → Disjoint (cycleArcs (c j)) (cycleArcs (c j'))

/--
Resolved true: Kühn, Lapinskas, Osthus and Patel proved Thomassen's conjecture with `f(k) = O(k²
log² k)`: every strongly `C k² log² k`-connected tournament has `k` edge-disjoint Hamilton cycles
(for `k = 1` this is Camion's theorem). Source: Open Problem Garden, Edge-disjoint Hamilton cycles
in highly strongly connected tournaments (node 47031; C. Thomassen),
http://www.openproblemgarden.org/op/edge_disjoint_hamilton_cycles; resolution: D. Kühn, J.
Lapinskas, D. Osthus and V. Patel, Proof of a conjecture of Thomassen on Hamilton cycles in highly
connected tournaments, Proc. Lond. Math. Soc. (3) 109 (2014), 733-762, doi:10.1112/plms/pdu019;
arXiv:1303.4213, Theorem 1.1: there is C > 0 such that for all k ≥ 2 every strongly C k^2 log^2
k-connected tournament contains k edge-disjoint Hamilton cycles; abstract: this proves Thomassen's
1982 conjecture, and Camion's theorem gives f(1) = 1, https://doi.org/10.1112/plms/pdu019.
-/
public theorem_wanted thomassenHamiltonCycles_holds : thomassenHamiltonCycles

end MathlibExt.GraphTheory.ThomassenEdgeDisjointHamiltonCyclesOpenGardenProblem47031Wanted
