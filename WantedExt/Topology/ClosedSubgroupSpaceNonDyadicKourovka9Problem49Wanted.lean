/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Non-dyadic spaces of closed subgroups of compact groups (Kourovka Notebook Problem 9.49)

Kourovka Notebook, Archive of Solved Problems, Problem 9.49 (I. V. Protasov, Yu. V. Tsybenko): let
`G` be a compact group of weight `> ω₂`. Is it true that the space of all closed subgroups of `G`
with respect to `E`-topology is non-dyadic?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WantedExt.Topology.VietorisSigmaCompactNoncompactSubgroupsKourovka8Problem63Wanted

@[expose] public section

namespace MathlibExt.Topology.ClosedSubgroupSpaceNonDyadicKourovka9Problem49Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.49 (I. V.
Protasov, Yu. V. Tsybenko). UnsolvedMath record UM-00700582 (`KOU-9.49`), dataset
ulamai/UnsolvedMath v1.8.0.

Reading. `G` is a Hausdorff compact group; its weight is the least cardinality of a base, so weight
`> ω₂` means that every base has more than `ℵ₂` members. The `E`-topology is the 8.63 module's
Vietoris topology; on a compact group its subbasic sets `{H | H ⊆ U}` coincide with the Chabauty
sets `{H | H ∩ K = ∅}` (`K = G \ U` compact), so it is the Chabauty topology used by Tsybenko and
the survey. A space is dyadic if it is a continuous image of a Cantor cube `{0, 1}^κ`. The module
covers the groups for which a source states the theorem: profinite (for compact groups, totally
disconnected) or abelian groups (Protasov's survey, Theorem 1.5; Tsybenko's main theorem, for
compact abelian groups, is that the space is dyadic iff the weight is less than `ℵ₂`, zbMATH Zbl
0617.22006). The Archive's "Yes" for every compact group rests on the same paper, whose zbMATH
reviewer notes that the main result extends to all compact groups; that general form is not stated
here.
-/

open MathlibExt.Topology.VietorisSigmaCompactNoncompactSubgroupsKourovka8Problem63Wanted
  (vietorisTopology)

/-- The space `X` is dyadic: a continuous image of a Cantor cube `{0, 1}^κ` (`Bool` discrete, the
product topology on `κ → Bool`). -/
def IsDyadic (X : Type) [TopologicalSpace X] : Prop :=
  ∃ (κ : Type) (f : (κ → Bool) → X), Continuous f ∧ Function.Surjective f

/-- Kourovka 9.49 (I. V. Protasov, Yu. V. Tsybenko) for profinite and for abelian compact groups:
if `G` is a compact group, profinite (totally disconnected) or abelian, of weight greater than
`ℵ₂` (every base of its topology has more than `ℵ₂` members), then the space of closed subgroups
of `G` with the `E`-topology is not dyadic. -/
def closedSubgroupSpaceNotDyadic : Prop :=
  ∀ (G : Type) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G],
    (TotallyDisconnectedSpace G ∨ ∀ a b : G, a * b = b * a) →
    (∀ B : Set (Set G), TopologicalSpace.IsTopologicalBasis B → Cardinal.aleph 2 < Cardinal.mk B) →
      ¬ @IsDyadic _ (vietorisTopology G)

/--
Resolved true for profinite and for abelian compact groups: if such a group has weight greater than
`ℵ₂`, its space of closed subgroups is not dyadic (Tsybenko 1986, as restated in Protasov's survey,
Theorem 1.5; the Kourovka Archive answers 9.49 "Yes" citing Tsybenko). Source: E. I. Khukhro and V.
D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.49 (I. V. Protasov, Yu. V.
Tsybenko); resolution: Yu. V. Tsybenko, Dyadic spaces of subgroups of topological groups, Ukr. Math.
J. 38 (1986), 542-545; restated in I. V. Protasov, Selective survey on spaces of closed subgroups of
topological groups, arXiv:1809.00139 (2018), Kourovka Archive, Problem 9.49: Yes, it is true
(Tsybenko); survey, Theorem 1.5: if G is profinite or compact abelian and w(G) > ℵ2 then S(G) is not
dyadic; zbMATH Zbl 0617.22006 (compact abelian G: S(G) dyadic iff w(G) < ℵ2),
https://doi.org/10.1007/BF01060948.
-/
public theorem_wanted closedSubgroupSpaceNotDyadic_holds : closedSubgroupSpaceNotDyadic

end MathlibExt.Topology.ClosedSubgroupSpaceNonDyadicKourovka9Problem49Wanted
