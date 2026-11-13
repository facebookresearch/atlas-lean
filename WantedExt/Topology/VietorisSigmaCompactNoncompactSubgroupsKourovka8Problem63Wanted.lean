/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# σ-compact spaces of closed subgroups and non-compact subgroups (Kourovka Notebook Problem 8.63)

Kourovka Notebook, Archive of Solved Problems, Problem 8.63 (I. V. Protasov): suppose that the space
of all closed subgroups of a locally compact group `G` is `σ`-compact in the `E`-topology. Is it
true that the set of closed non-compact subgroups of `G` is at most countable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

namespace MathlibExt.Topology.VietorisSigmaCompactNoncompactSubgroupsKourovka8Problem63Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.63 (I. V.
Protasov). UnsolvedMath record UM-00700512 (`KOU-8.63`), dataset ulamai/UnsolvedMath v1.8.0.

`G` is a Hausdorff locally compact topological group. The `E`-topology on the closed subgroups is
the Vietoris topology, with subbase `{H | H ⊆ U}` and `{H | H ∩ U ≠ ∅}`, `U` open (Protasov writes
`exp X` for the space of closed subsets). Basis: Piskunov's paper works in the Vietoris topology
(zbMATH review, Zbl 0723.22004: Theorem 4, the space of closed subgroups with the Vietoris topology
is σ-compact iff `G` is σ-compact with countably many non-compact closed subgroups), and Protasov's
survey arXiv:1809.00139 defines the Vietoris topology in §2 and lists there both the σ-compact case
(§2.1, ref. [33]) and Theorem 2.3 with the corollary that the space is a k-space for every locally
compact group of countable weight (ref. [35], Protasov 1986, pp. 64-66, the paper the Notebook cites
for 9.46, which it poses for the `E`-topology). The Chabauty reading is excluded: the Chabauty space
of a locally compact group is always compact (survey §1.1), so the hypothesis would always hold and
`ℝ`, with uncountably many closed non-compact subgroups `aℤ`, would refute the statement.
-/

/-- The `E`-topology (Vietoris topology) on the closed subgroups of `G`, with subbasic open sets
`{H | H ⊆ U}` and `{H | H ∩ U ≠ ∅}` for open `U`. -/
abbrev vietorisTopology (G : Type) [TopologicalSpace G] [Group G] :
    TopologicalSpace {H : Subgroup G // IsClosed (H : Set G)} :=
  TopologicalSpace.generateFrom
    ({S | ∃ U : Set G, IsOpen U ∧ S = {H | (H.1 : Set G) ⊆ U}} ∪
      {S | ∃ U : Set G, IsOpen U ∧ S = {H | ((H.1 : Set G) ∩ U).Nonempty}})

/-- Kourovka 8.63 (I. V. Protasov): if the space of closed subgroups of a locally compact group `G`
is `σ`-compact in the `E`-topology, then `G` has at most countably many closed non-compact
subgroups. -/
def sigmaCompactSubgroupSpaceCountableNoncompact : Prop :=
  ∀ (G : Type) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G], @SigmaCompactSpace _ (vietorisTopology G) →
    {H : {H : Subgroup G // IsClosed (H : Set G)} | ¬ IsCompact (H.1 : Set G)}.Countable

/--
Resolved true: the Kourovka Archive answers 8.63 "Yes, it is", citing Piskunov, Cardinality of open
σ-compact sets in the space of noncompact subgroups of a topological group (1988), whose Theorem 4
(zbMATH Zbl 0723.22004) states that the space of closed subgroups with the Vietoris topology is
σ-compact exactly when `G` is σ-compact and has countably many non-compact closed subgroups. Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.63 (I. V. Protasov);
resolution: A. G. Piskunov, Cardinality of open σ-compact sets in the space of noncompact subgroups
of a topological group, Ukrainian Math. J. 40 (1988), 679-683, Kourovka Archive, Problem 8.63: Yes,
it is (Piskunov); paper, Theorem 4 (zbMATH Zbl 0723.22004), https://doi.org/10.1007/BF01057194.
-/
public theorem_wanted sigmaCompactSubgroupSpaceCountableNoncompact_holds :
    sigmaCompactSubgroupSpaceCountableNoncompact

end MathlibExt.Topology.VietorisSigmaCompactNoncompactSubgroupsKourovka8Problem63Wanted
