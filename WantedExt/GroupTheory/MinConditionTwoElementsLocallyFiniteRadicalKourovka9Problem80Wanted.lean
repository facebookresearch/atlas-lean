/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 2-elements and the locally finite radical (Kourovka Notebook Problem 9.80)

Kourovka Notebook, Archive of Solved Problems, Problem 9.80 (V. P. Shunkov): are the `2`-elements of
a group with the minimum condition contained in its locally finite radical?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Nat.Defs
public import WantedExt.GroupTheory.LocallyFiniteSimpleFiniteRankKourovka1Problem23Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.MinConditionTwoElementsLocallyFiniteRadicalKourovka9Problem80Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.80 (V. P.
Shunkov). UnsolvedMath record UM-00700613 (`KOU-9.80`), dataset ulamai/UnsolvedMath v1.8.0.

The minimum condition is on subgroups. The minimum condition on subgroups is `WellFoundedLT
(Subgroup G)`: every non-empty set of subgroups has a minimal member. A `2`-element has order a
power of `2`. Locally finite is the 1.23 entry's `IsLocallyFinite`: every finite subset generates a
finite subgroup, i.e. every finitely generated subgroup is finite. The locally finite radical is the
largest locally finite normal subgroup, which contains every locally finite normal subgroup, so
lying in it means lying in some locally finite normal subgroup.
-/

open MathlibExt.GroupTheory.LocallyFiniteSimpleFiniteRankKourovka1Problem23Wanted

/-- Kourovka 9.80 (V. P. Shunkov): in a group with the minimum condition on subgroups every
`2`-element (element of `2`-power order) lies in the locally finite radical, i.e. in some locally
finite normal subgroup (the locally finite radical is the largest one, and contains them all). -/
def minConditionTwoElementsInLFRadical : Prop :=
  ∀ (G : Type) [Group G], WellFoundedLT (Subgroup G) → ∀ g : G, (∃ n : ℕ, g ^ 2 ^ n = 1) →
    ∃ N : Subgroup G, N.Normal ∧ IsLocallyFinite N ∧ g ∈ N

/--
Resolved false: the Kourovka Archive answers 9.80 "Not necessarily", citing Ol'shanskii's book: some
group with the minimum condition on subgroups has a `2`-element outside its locally finite radical.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.80 (V. P.
Shunkov); resolution: A. Yu. Ol'shanskii, Geometry of defining relations in groups, Kluwer,
Dordrecht, 1991, Kourovka Archive of Solved Problems, Problem 9.80: Not necessarily,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted minConditionTwoElementsInLFRadical_refuted :
    ¬ minConditionTwoElementsInLFRadical

end MathlibExt.GroupTheory.MinConditionTwoElementsLocallyFiniteRadicalKourovka9Problem80Wanted
