/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The space of closed subgroups is a k-space (Kourovka Notebook Problem 9.46)

Kourovka Notebook, Archive of Solved Problems, Problem 9.46 (I. V. Protasov): let `G` be a locally
compact group of countable weight and `L(G)` the space of all its closed subgroups equipped with the
`E`-topology. Then is `L(G)` a `k`-space?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import WantedExt.Topology.VietorisSigmaCompactNoncompactSubgroupsKourovka8Problem63Wanted

@[expose] public section

namespace MathlibExt.Topology.ClosedSubgroupSpaceKSpaceKourovka9Problem46Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.46 (I. V.
Protasov). UnsolvedMath record UM-00700579 (`KOU-9.46`), dataset ulamai/UnsolvedMath v1.8.0.

Reading. `G` is a Hausdorff locally compact group; countable weight is second countability. The
`E`-topology is the Vietoris topology on the closed subgroups (the 8.63 module's `vietorisTopology`;
Protasov's survey arXiv:1809.00139, §2). A `k`-space is a space whose topology is determined by its
compact subsets; Mathlib's `CompactlyGeneratedSpace` (topology coinduced by the maps from compact
Hausdorff spaces) is that notion for Hausdorff spaces, and the Vietoris space of closed subsets of a
regular space such as `G` is Hausdorff.
-/

open MathlibExt.Topology.VietorisSigmaCompactNoncompactSubgroupsKourovka8Problem63Wanted
  (vietorisTopology)

/-- Kourovka 9.46 (I. V. Protasov): for a locally compact group `G` of countable weight, the space
of closed subgroups of `G` with the `E`-topology (Vietoris topology) is a `k`-space. -/
def closedSubgroupSpaceIsKSpace : Prop :=
  ∀ (G : Type) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G], @CompactlyGeneratedSpace _ (vietorisTopology G)

/--
Resolved true: for a locally compact group of countable weight the space of closed subgroups with
the Vietoris topology is a `k`-space (Protasov 1986, as the Kourovka Archive records; restated in
Protasov's survey, §2.1, as a corollary of Theorem 2.3). Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 9.46 (I. V. Protasov); resolution: I. V. Protasov, Dokl.
Akad. Nauk Ukr. SSR Ser. A 10 (1986), 64-66 (Russian); restated in I. V. Protasov, Selective survey
on spaces of closed subgroups of topological groups, arXiv:1809.00139 (2018), Kourovka Archive,
Problem 9.46: Yes (Protasov); survey, §2.1, corollary of Theorem 2.3: S(G) is a k-space for each
locally compact group G of countable weight, https://arxiv.org/abs/1809.00139.
-/
public theorem_wanted closedSubgroupSpaceIsKSpace_holds : closedSubgroupSpaceIsKSpace

end MathlibExt.Topology.ClosedSubgroupSpaceKSpaceKourovka9Problem46Wanted
