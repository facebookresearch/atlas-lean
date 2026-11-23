/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Locally compact group topologies with the same closed subgroups (Kourovka Notebook Problem 3.35)

Kourovka Notebook, Archive of Solved Problems, Problem 3.35 (K. Ross; Yu. N. Mukhin): suppose that a
group `G` admits two topologies `σ` and `τ` yielding locally compact topological groups `G_σ` and
`G_τ`. If the sets of closed subgroups in `G_σ` and `G_τ` are the same, does it follow that `G_σ`
and `G_τ` are topologically isomorphic?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

namespace MathlibExt.GroupTheory.LocallyCompactClosedSubgroupsTopologyKourovka3Problem35Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.35 (K. Ross;
Yu. N. Mukhin). UnsolvedMath record UM-00700185 (`KOU-3.35`), dataset ulamai/UnsolvedMath v1.8.0.

The two topologies are terms `σ τ : TopologicalSpace G`; locally compact topological groups are
taken Hausdorff, as is standard in this setting. Topologically isomorphic means some group
automorphism `φ` of `G` is a homeomorphism `(G, σ) → (G, τ)`.
-/

/-- Kourovka 3.35 (K. Ross; Yu. N. Mukhin): if two topologies `σ` and `τ` on a group `G` both make
it a Hausdorff locally compact topological group, and the two have the same closed subgroups, then
`(G, σ)` and `(G, τ)` are topologically isomorphic. -/
def sameClosedSubgroupsTopologicallyIsomorphic : Prop :=
  ∀ (G : Type) [Group G] (σ τ : TopologicalSpace G),
    @IsTopologicalGroup G σ _ → @IsTopologicalGroup G τ _ →
    @LocallyCompactSpace G σ → @LocallyCompactSpace G τ → @T2Space G σ → @T2Space G τ →
    (∀ H : Subgroup G, @IsClosed G σ (H : Set G) ↔ @IsClosed G τ (H : Set G)) →
    ∃ φ : G ≃* G, @Continuous G G σ τ φ ∧ @Continuous G G τ σ φ.symm

/--
Resolved false: the Kourovka Archive answers 3.35 "Not always", citing Moskalenko (Ukrain. Math. J.
30 (1978)): two locally compact group topologies on one group can have the same closed subgroups
without being topologically isomorphic. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 3.35 (K. Ross; Yu. N. Mukhin); resolution: A. I. Moskalenko, Ukrain. Math.
J. 30 (1978), 199-201, Kourovka Archive, Problem 3.35: Not always,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted sameClosedSubgroupsTopologicallyIsomorphic_refuted :
    ¬ sameClosedSubgroupsTopologicallyIsomorphic

end MathlibExt.GroupTheory.LocallyCompactClosedSubgroupsTopologyKourovka3Problem35Wanted
