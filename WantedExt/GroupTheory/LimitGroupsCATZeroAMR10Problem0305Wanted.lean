/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Limit groups are CAT(0) (Bestvina, Q 3.5)

M. Bestvina, Questions in Geometric Group Theory, Q 3.5 (Z. Sela): conjecture: limit groups are
CAT(0). The list recalls that a group is a limit group if and only if it is ω-residually free: for
any finite subset `F` of `G` there is a homomorphism from `G` to a free group whose restriction to
`F` is injective.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import WantedExt.Geometry.CATZeroSpaceShared

@[expose] public section

namespace MathlibExt.GroupTheory.LimitGroupsCATZeroAMR10Problem0305Wanted

/-!
Source: M. Bestvina, Questions in Geometric Group Theory (updated July 2004), Q 3.5 (Z. Sela),
https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf. UnsolvedMath record UM-01100305
(`AMR-010-0305`), dataset ulamai/UnsolvedMath v1.8.0.

A limit group is a finitely generated ω-residually free group (the list's §3.1 and
Alibegović–Bestvina's definition). A CAT(0) group acts properly discontinuously and cocompactly by
isometries on a CAT(0) space (Alibegović–Bestvina §1, whose spaces are proper); CAT(0) is
`IsCATZero` from `WantedExt.Geometry.CATZeroSpaceShared`, as in Q 1.17's module.
`OpenConjectures/GroupTheory/MeasureEquivalenceOfLimitAndFreeGroups` has an equivalent
`IsLimitGroup` (finitely generated and fully residually free, via maps to `F₂`); that entry is not
importable from WantedExt.
-/

open MathlibExt.Geometry.CATZeroSpaceShared

/-- `G` is a limit group (`ω`-residually free): finitely generated, and for every finite subset `W`
of `G` there is a homomorphism from `G` to a free group whose restriction to `W` is injective. -/
def IsLimitGroup (G : Type) [Group G] : Prop :=
  Group.FG G ∧ ∀ W : Finset G, ∃ (X : Type) (φ : G →* FreeGroup X), Set.InjOn φ W

/-- Bestvina Q 3.5: every limit group is CAT(0), i.e. acts properly discontinuously and
cocompactly by isometries on a proper CAT(0) space. -/
def limitGroupsAreCATZero : Prop :=
  ∀ (G : Type) [Group G], IsLimitGroup G →
    ∃ (X : Type) (_ : MetricSpace X) (_ : ProperSpace X) (_ : MulAction G X),
      IsCATZero X ∧ IsIsometricSMul G X ∧ ProperlyDiscontinuousSMul G X ∧
        ∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ g : G, x ∈ (fun y => g • y) '' K

/--
Resolved true: Alibegović and Bestvina proved that every limit group acts properly discontinuously
and cocompactly by isometries on a proper CAT(0) space (with isolated flats). Source: M. Bestvina,
Questions in Geometric Group Theory (updated July 2004), Q 3.5 (Z. Sela),
https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf; resolution: E. Alibegović and M.
Bestvina, Limit groups are CAT(0), J. London Math. Soc. (2) 74 (2006), no. 1, 259-272, DOI
10.1112/S0024610706023155, arXiv:math/0410198, Abstract and Theorem 4.9: every limit group acts
geometrically on a CAT(0) space with the isolated flats property; §1: a CAT(0) group 'acts
geometrically, i.e. properly discontinuously and cocompactly by isometries, on a CAT(0) space', 'All
of our (locally) CAT(0) spaces will be proper', and a limit group is a finitely generated group L
such that every finite W ⊂ L has a homomorphism to a free group injective on W,
https://arxiv.org/abs/math/0410198.
-/
public theorem_wanted limitGroupsAreCATZero_holds : limitGroupsAreCATZero

end MathlibExt.GroupTheory.LimitGroupsCATZeroAMR10Problem0305Wanted
