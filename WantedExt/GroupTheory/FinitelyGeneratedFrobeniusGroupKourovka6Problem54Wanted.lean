/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Infinite finitely generated Frobenius groups (Kourovka Notebook Problem 6.54)

Kourovka Notebook, Archive of Solved Problems, Problem 6.54 (V. P. Shunkov): are there infinite
finitely generated Frobenius groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import WantedExt.GroupTheory.FrobeniusGroupShared

@[expose] public section

namespace MathlibExt.GroupTheory.FinitelyGeneratedFrobeniusGroupKourovka6Problem54Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.54 (V. P.
Shunkov). UnsolvedMath record UM-00700396 (`KOU-6.54`), dataset ulamai/UnsolvedMath v1.8.0.

Frobenius groups are `IsFrobeniusGroup F H` of `FrobeniusGroupShared`, the definition of Problem
6.53: `G = F ⋊ H` with `H ∩ Hᵍ = 1` for `g ∉ H` and `F \ {1} = G \ ⋃ Hᵍ`, plus non-trivial `F` and
`H` (with `H = 1` every group would be the kernel of the Frobenius group `G ⋊ 1`).
-/

open MathlibExt.GroupTheory.FrobeniusGroupShared (IsFrobeniusGroup)

/-- Kourovka 6.54 (V. P. Shunkov): there is an infinite finitely generated Frobenius group. -/
def existsInfiniteFGFrobeniusGroup : Prop :=
  ∃ (G : Type) (_ : Group G) (F H : Subgroup G), IsFrobeniusGroup F H ∧ Group.FG G ∧ Infinite G

/--
Resolved true: the Kourovka Archive answers 6.54 "Yes, such groups exist", citing Sozutov (1994):
some infinite finitely generated group is a Frobenius group. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 6.54 (V. P. Shunkov); resolution: A. I. Sozutov, On the
structure of the noninvariant factor in some Frobenius groups, Siberian Math. J. 35, no. 4 (1994),
795-801, zbMATH review Zbl 0851.20039: the article constructs a periodic, not locally finite
Frobenius group, solving Problem 6.54; Kourovka Archive, Problem 6.54: Yes, such groups exist
(Sozutov), https://doi.org/10.1007/BF02106623.
-/
public theorem_wanted existsInfiniteFGFrobeniusGroup_holds : existsInfiniteFGFrobeniusGroup

end MathlibExt.GroupTheory.FinitelyGeneratedFrobeniusGroupKourovka6Problem54Wanted
