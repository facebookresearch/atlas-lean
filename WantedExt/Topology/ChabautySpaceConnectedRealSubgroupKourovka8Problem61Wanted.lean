/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Connectedness of the Chabauty space of a group containing ℝ (Kourovka Notebook Problem 8.61)

Kourovka Notebook, Archive of Solved Problems, Problem 8.61 (I. V. Protasov): suppose that a locally
compact group `G` contains a subgroup that is topologically isomorphic to the additive group of the
field of real numbers with natural topology. Is the space of all closed subgroups of `G` connected
in the Chabauty topology?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Topology.ChabautySpaceConnectedRealSubgroupKourovka8Problem61Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.61 (I. V.
Protasov). UnsolvedMath record UM-00700510 (`KOU-8.61`), dataset ulamai/UnsolvedMath v1.8.0.

`G` is a Hausdorff locally compact topological group. The Chabauty topology on the closed subgroups
has the subbase `{H | H ∩ K = ∅}`, `K` compact, and `{H | H ∩ U ≠ ∅}`, `U` open (Protasov's survey,
§1.1). A subgroup topologically isomorphic to `ℝ` is the image of a homomorphism `Multiplicative ℝ
→* G` that is a topological embedding.
-/

/-- The Chabauty topology on the closed subgroups of `G`, with subbasic open sets
`{H | H ∩ K = ∅}` for compact `K` and `{H | H ∩ U ≠ ∅}` for open `U`. -/
abbrev chabautyTopology (G : Type) [TopologicalSpace G] [Group G] :
    TopologicalSpace {H : Subgroup G // IsClosed (H : Set G)} :=
  TopologicalSpace.generateFrom
    ({S | ∃ K : Set G, IsCompact K ∧ S = {H | Disjoint (H.1 : Set G) K}} ∪
      {S | ∃ U : Set G, IsOpen U ∧ S = {H | ((H.1 : Set G) ∩ U).Nonempty}})

/-- Kourovka 8.61 (I. V. Protasov): if a locally compact group `G` contains a subgroup
topologically isomorphic to the additive group `ℝ` (a topological embedding of `ℝ` as a group
homomorphism), then the space of closed subgroups of `G` is connected in the Chabauty topology. -/
def chabautySpaceConnectedOfRealSubgroup : Prop :=
  ∀ (G : Type) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G], (∃ φ : Multiplicative ℝ →* G, Topology.IsEmbedding φ) →
    @ConnectedSpace _ (chabautyTopology G)

/--
Resolved false: the Kourovka Archive answers 8.61 "No, not always", citing Tsybenko (1983): the
group of matrices `[[1, z₁, r], [0, 1, z₂], [0, 0, 1]]`, `z₁, z₂ ∈ ℤ`, `r ∈ ℝ`, is locally compact
and contains a central subgroup topologically isomorphic to `ℝ`, but its space of closed subgroups
is not connected. (For locally compact abelian groups the answer is yes: the Chabauty space is
connected exactly when there is such a subgroup, Protasov's survey arXiv:1809.00139, Theorem 1.8.)
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.61 (I. V.
Protasov); resolution: Yu. V. Tsybenko, Abstracts of the 17th All-Union Algebraic Conference, Part
1, Minsk, 1983, 213 (Russian), Kourovka Archive, Problem 8.61: No, not always; the group H of
matrices [[1, z₁, r], [0, 1, z₂], [0, 0, 1]] with z₁, z₂ ∈ ℤ and r ∈ ℝ is locally compact and
contains a central subgroup topologically isomorphic to ℝ, but L(H) is not connected,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted chabautySpaceConnectedOfRealSubgroup_refuted :
    ¬ chabautySpaceConnectedOfRealSubgroup

end MathlibExt.Topology.ChabautySpaceConnectedRealSubgroupKourovka8Problem61Wanted
