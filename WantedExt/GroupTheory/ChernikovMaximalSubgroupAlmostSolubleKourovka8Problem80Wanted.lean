/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Locally finite groups with a Chernikov maximal subgroup (Kourovka Notebook Problem 8.80)

Kourovka Notebook, Archive of Solved Problems, Problem 8.80 (B. Hartley): let `G` be a locally
finite group containing a maximal subgroup which is Chernikov. Is `G` almost soluble?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Solvable
public import WantedExt.GroupTheory.ChernikovSubgroupLatticeDimensionKourovka11Problem116Wanted
public import WantedExt.GroupTheory.LocallyFiniteSimpleFiniteRankKourovka1Problem23Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.ChernikovMaximalSubgroupAlmostSolubleKourovka8Problem80Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.80 (B.
Hartley). UnsolvedMath record UM-00700528 (`KOU-8.80`), dataset ulamai/UnsolvedMath v1.8.0.

Locally finite is the 1.23 entry's `IsLocallyFinite`: every finite subset generates a finite
subgroup, i.e. every finitely generated subgroup is finite. A maximal subgroup is a coatom of the
subgroup lattice. A Chernikov group is the 11.116 entry's `IsChernikov`: a normal subgroup of finite
index isomorphic to a direct product of finitely many quasicyclic groups. Almost soluble means
having a soluble subgroup of finite index.
-/

open MathlibExt.GroupTheory.LocallyFiniteSimpleFiniteRankKourovka1Problem23Wanted
open MathlibExt.GroupTheory.ChernikovSubgroupLatticeDimensionKourovka11Problem116Wanted

/-- Kourovka 8.80 (B. Hartley): a locally finite group with a maximal subgroup that is a Chernikov
group (`IsChernikov`, from the 11.116 entry) is almost soluble (has a soluble subgroup of finite
index). -/
def chernikovMaximalAlmostSoluble : Prop :=
  ∀ (G : Type) [Group G], IsLocallyFinite G → ∀ M : Subgroup G, IsCoatom M → IsChernikov M →
    ∃ S : Subgroup G, S.FiniteIndex ∧ Group.IsSolvable S

/--
Resolved true: Hartley gives an essentially complete description of locally finite groups with a
Chernikov maximal subgroup, answering Question 8.80; the Kourovka Archive answers "Yes, it is": such
a group has a soluble subgroup of finite index. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 8.80 (B. Hartley); resolution: B. Hartley, On locally finite
groups with a Chernikov maximal subgroup, Algebra and Logic 37 (1998), 56-58 (Russian original:
Algebra i Logika 37 (1998), no. 1, 101-106), abstract: an essentially complete description of
locally finite groups with a Chernikov maximal subgroup, which answers Question 8.80; Kourovka
Archive of Solved Problems, Problem 8.80: Yes, it is, https://doi.org/10.1007/BF02684085.
-/
public theorem_wanted chernikovMaximalAlmostSoluble_holds : chernikovMaximalAlmostSoluble

end MathlibExt.GroupTheory.ChernikovMaximalSubgroupAlmostSolubleKourovka8Problem80Wanted
