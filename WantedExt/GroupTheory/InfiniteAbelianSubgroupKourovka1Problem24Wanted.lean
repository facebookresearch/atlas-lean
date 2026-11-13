/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Infinite abelian subgroups of infinite groups (Kourovka Notebook Problem 1.24)

Kourovka Notebook, Archive of Solved Problems, Problem 1.24 (M. I. Kargapolov): does every infinite
group possess an infinite abelian subgroup?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Finite.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.InfiniteAbelianSubgroupKourovka1Problem24Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.24 (M. I.
Kargapolov). UnsolvedMath record UM-00700019 (`KOU-1.24`), dataset ulamai/UnsolvedMath v1.8.0.

Groups are taken in `Type`; the counterexample (a free Burnside group) is countable.
-/

/-- Kourovka 1.24 (M. I. Kargapolov): every infinite group has an infinite abelian subgroup. -/
def infiniteGroupHasInfiniteAbelianSubgroup : Prop :=
  ∀ (G : Type) [Group G], Infinite G →
    ∃ H : Subgroup G, (∀ x ∈ H, ∀ y ∈ H, x * y = y * x) ∧ (H : Set G).Infinite

/--
Resolved false: the Kourovka Archive answers 1.24 "No", citing Novikov and Adian: for `m ≥ 2` and
odd `n ≥ 4381` the free Burnside group `B(m, n)` is infinite and every abelian subgroup of it is
cyclic, hence finite. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 1.24 (M. I. Kargapolov); resolution: P. S. Novikov and S. I. Adian, Math. USSR-Izv. 2
(1968), 1131-1144, Kourovka Archive, Problem 1.24 (No); every abelian subgroup of the infinite free
Burnside group B(m, n), m ≥ 2, n odd ≥ 4381, is cyclic (Encyclopedia of Mathematics, Burnside
group).
-/
public theorem_wanted infiniteGroupHasInfiniteAbelianSubgroup_refuted :
    ¬ infiniteGroupHasInfiniteAbelianSubgroup

end MathlibExt.GroupTheory.InfiniteAbelianSubgroupKourovka1Problem24Wanted
