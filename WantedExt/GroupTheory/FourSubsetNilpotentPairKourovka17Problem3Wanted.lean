/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups in which four elements contain a nilpotent pair (Kourovka Notebook Problem 17.3)

Kourovka Notebook, Archive of Solved Problems, Problem 17.3 (A. Abdollahi): let `G` be a group in
which every 4-element subset contains two elements generating a nilpotent subgroup. Is it true that
every 2-generated subgroup of `G` is nilpotent?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.FourSubsetNilpotentPairKourovka17Problem3Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.3 (A.
Abdollahi). UnsolvedMath record UM-00701305 (`KOU-17.3`), dataset ulamai/UnsolvedMath v1.8.0.

The two elements are required to be distinct (one element always generates a nilpotent subgroup).
Groups are taken in `Type`.
-/

/-- Kourovka 17.3 (A. Abdollahi): if every 4-element subset of a group `G` contains two distinct
elements generating a nilpotent subgroup, then every 2-generated subgroup of `G` is nilpotent. -/
def fourSubsetNilpotentPairTwoGeneratedNilpotent : Prop :=
  ∀ (G : Type) [Group G],
    (∀ s : Finset G, s.card = 4 →
      ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ Group.IsNilpotent (Subgroup.closure {x, y})) →
    ∀ x y : G, Group.IsNilpotent (Subgroup.closure {x, y})

/--
Resolved false: the Kourovka Archive answers 17.3 "No, not always", citing Sozutov (2019): some
group in which every 4-element subset contains two elements generating a nilpotent subgroup has a
2-generated subgroup that is not nilpotent. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 17.3 (A. Abdollahi); resolution: A. I. Sozutov, Siberian Math. J. 60
(2019), 1099-1100, Kourovka Archive, Problem 17.3 (No, not always).
-/
public theorem_wanted fourSubsetNilpotentPairTwoGeneratedNilpotent_refuted :
    ¬ fourSubsetNilpotentPairTwoGeneratedNilpotent

end MathlibExt.GroupTheory.FourSubsetNilpotentPairKourovka17Problem3Wanted
