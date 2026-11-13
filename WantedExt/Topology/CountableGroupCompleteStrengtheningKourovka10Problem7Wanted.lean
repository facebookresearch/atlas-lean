/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Refining first-countable group topologies to complete ones (Kourovka Notebook Problem 10.7)

Kourovka Notebook, Archive of Solved Problems, Problem 10.7 (V. I. Arnautov): is it true that in a
countable group `G`, any non-discrete group topology satisfying the first axiom of countability can
be strengthened up to a non-discrete group topology such that `G` becomes a complete topological
group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.Algebra.Group.GroupTopology

@[expose] public section

namespace MathlibExt.Topology.CountableGroupCompleteStrengtheningKourovka10Problem7Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.7 (V. I.
Arnautov). UnsolvedMath record UM-00700624 (`KOU-10.7`), dataset ulamai/UnsolvedMath v1.8.0.

The given group topology is assumed Hausdorff, as usual in this setting; a finer topology is then
Hausdorff as well. Strengthening means a finer topology (`σ ≤ τ` in Mathlib's order on
`GroupTopology`, whose bottom element is the discrete topology). Completeness is Raikov
completeness, for the two-sided uniformity: the weakest of the standard notions, implied by
completeness for the left or the right uniformity.
-/

/-- The group `G` is complete for the topology `t` in Raikov's sense: every proper filter that is
Cauchy for the two-sided uniformity (for every neighbourhood `U` of `1` it contains a set `A` with
`x⁻¹ y ∈ U` and `y x⁻¹ ∈ U` for all `x, y ∈ A`) converges. -/
def IsRaikovComplete {G : Type*} [Group G] (t : TopologicalSpace G) : Prop :=
  ∀ F : Filter G, F.NeBot →
    (∀ U ∈ @nhds G t 1, ∃ A ∈ F, ∀ x ∈ A, ∀ y ∈ A, x⁻¹ * y ∈ U ∧ y * x⁻¹ ∈ U) →
      ∃ g : G, F ≤ @nhds G t g

/-- Kourovka 10.7 (V. I. Arnautov): in a countable group `G`, every non-discrete Hausdorff group
topology satisfying the first axiom of countability can be strengthened (refined) to a
non-discrete group topology in which `G` is a complete topological group. -/
def countableGroupTopologyStrengthening : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (τ : GroupTopology G),
    @T2Space G τ.toTopologicalSpace → @FirstCountableTopology G τ.toTopologicalSpace → τ ≠ ⊥ →
      ∃ σ : GroupTopology G, σ ≤ τ ∧ σ ≠ ⊥ ∧ IsRaikovComplete σ.toTopologicalSpace

/--
Resolved true: the Kourovka Archive answers "Yes, it is", citing Arnautov and Kabanova (1990): in a
countable group every non-discrete first-countable group topology can be strengthened to a
non-discrete group topology in which the group is complete. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 10.7 (V. I. Arnautov); resolution: V. I. Arnautov and E.
I. Kabanova, Siberian Math. J. 31 (1990), 1-10, Kourovka Archive, Problem 10.7 ("Yes, it is").
-/
public theorem_wanted countableGroupTopologyStrengthening_holds :
    countableGroupTopologyStrengthening

end MathlibExt.Topology.CountableGroupCompleteStrengtheningKourovka10Problem7Wanted
