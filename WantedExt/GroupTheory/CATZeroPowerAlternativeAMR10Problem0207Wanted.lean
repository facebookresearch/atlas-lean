/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The power alternative for CAT(0) groups (Bestvina, Q 2.7)

M. Bestvina, Questions in Geometric Group Theory, Q 2.7 (D. Wise): let `G` act properly
discontinuously and cocompactly on a CAT(0) space (or let `G` be automatic). Consider two elements
`a, b` of `G`. Does there exist `n > 0` such that either the subgroup `⟨aⁿ, bⁿ⟩` is free or `⟨aⁿ,
bⁿ⟩` is abelian?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import WantedExt.Geometry.CATZeroSpaceShared

@[expose] public section

namespace MathlibExt.GroupTheory.CATZeroPowerAlternativeAMR10Problem0207Wanted

/-!
Source: M. Bestvina, Questions in Geometric Group Theory (updated July 2004), Q 2.7 (D. Wise),
https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf. UnsolvedMath record UM-01100207
(`AMR-010-0207`), dataset ulamai/UnsolvedMath v1.8.0.

The CAT(0) case: `G` acts by isometries (`IsIsometricSMul`), properly discontinuously
(`ProperlyDiscontinuousSMul`) and cocompactly on a proper CAT(0) space (`IsCATZero`,
`WantedExt.Geometry.CATZeroSpaceShared`: nonempty geodesic space with the Berg–Nikolaev four-point
condition), as in Q 1.17's module. 'Free' is `IsFreeGroup` of the subgroup (free of any rank,
including trivial and cyclic); 'abelian' means its elements commute. The automatic case, which the
counterexample does not address, is not formalized.
-/

open MathlibExt.Geometry.CATZeroSpaceShared

/-- Wise's question (Bestvina Q 2.7), CAT(0) case: if a group `G` acts properly discontinuously
and cocompactly by isometries on a proper CAT(0) space, then for any `a b : G` some `n > 0` makes
`⟨aⁿ, bⁿ⟩` free or abelian. -/
def catZeroPowerAlternative : Prop :=
  ∀ (G : Type) [Group G] (X : Type) [MetricSpace X] [ProperSpace X] [MulAction G X],
    IsCATZero X → IsIsometricSMul G X → ProperlyDiscontinuousSMul G X →
      (∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ g : G, x ∈ (fun y => g • y) '' K) →
      ∀ a b : G, ∃ n : ℕ, 0 < n ∧
        (IsFreeGroup (Subgroup.closure ({a ^ n, b ^ n} : Set G)) ∨
          ∀ x ∈ Subgroup.closure ({a ^ n, b ^ n} : Set G),
            ∀ y ∈ Subgroup.closure ({a ^ n, b ^ n} : Set G), x * y = y * x)

/--
Resolved false: Leary and Minasyan's group `G_P` acts properly discontinuously and cocompactly by
isometries on the CAT(0) space `E² × T` (`T` a regular tree), and for its elements `a, t` no power
`n > 0` makes `⟨aⁿ, tⁿ⟩` free or abelian. Source: M. Bestvina, Questions in Geometric Group Theory
(updated July 2004), Q 2.7 (D. Wise),
https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf; resolution: I. J. Leary and A.
Minasyan, Commensurating HNN extensions: nonpositive curvature and biautomaticity, Geom. Topol. 25
(2021), 1819-1860, arXiv:1907.03515, §1: the group G_P acts geometrically on E² × T; for any n ≠ 0
the subgroup ⟨aⁿ, tⁿ⟩ < G_P is not abelian and contains a finite-index subgroup of ⟨a, b⟩ ≅ ℤ², so
it is not free (Corollary 9.6); 'Thus the elements a, t ∈ G_P give the first negative answer to a
question of Wise concerning a strong version of the Tits Alternative for CAT(0) groups [Question
2.7]'; the groups G_{k,2}, k ∈ {-3, -1, 1, 3}, give further counterexamples,
https://arxiv.org/abs/1907.03515.
-/
public theorem_wanted catZeroPowerAlternative_refuted : ¬ catZeroPowerAlternative

end MathlibExt.GroupTheory.CATZeroPowerAlternativeAMR10Problem0207Wanted
