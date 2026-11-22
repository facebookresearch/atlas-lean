/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Infinite finitely generated simple amenable groups (Kourovka Notebook Problem 15.5)

Kourovka Notebook, Archive of Solved Problems, Problem 15.5 (P. de la Harpe; well-known problem):
does there exist an infinite finitely generated group which is simple and amenable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Subgroup.Simple
public import MathlibExt.GroupTheory.AmenableGroup

@[expose] public section

namespace MathlibExt.GroupTheory.InfiniteSimpleAmenableGroupKourovka15Problem5Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.5 (P. de la
Harpe). UnsolvedMath record UM-00701093 (`KOU-15.5`), dataset ulamai/UnsolvedMath v1.8.0.

Amenability is MathlibExt's Følner-condition `IsAmenable`, equivalent for discrete groups to the
existence of an invariant mean; simplicity is Mathlib's `IsSimpleGroup`.
-/

/-- Kourovka 15.5 (P. de la Harpe): there is an infinite finitely generated simple amenable
group. -/
def infiniteFGSimpleAmenableGroup : Prop :=
  ∃ (G : Type) (_ : Group G), Infinite G ∧ Group.FG G ∧ IsSimpleGroup G ∧ IsAmenable G

/--
Resolved true: the Kourovka Archive answers 15.5 "Yes, it does" (Juschenko and Monod; another
example by Nekrashevych): there is an infinite finitely generated simple amenable group. Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.5 (P. de la Harpe);
resolution: K. Juschenko and N. Monod, Cantor systems, piecewise translations and simple amenable
groups, Ann. of Math. (2) 178 (2013), no. 2, 775-787, arXiv:1204.2132, abstract (the first examples
of finitely generated simple groups that are amenable and infinite); Kourovka Archive, Problem 15.5
(answer: Yes, it does; another example in V. Nekrashevych, Ann. of Math. 187 (2018), 667-719),
https://arxiv.org/abs/1204.2132.
-/
public theorem_wanted infiniteFGSimpleAmenableGroup_holds : infiniteFGSimpleAmenableGroup

end MathlibExt.GroupTheory.InfiniteSimpleAmenableGroupKourovka15Problem5Wanted
