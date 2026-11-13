/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CAT(0) groups whose direct powers have bounded rank (Bestvina, Q 1.17)

M. Bestvina, Questions in Geometric Group Theory, Q 1.17 (Dani Wise): find "nice" (e.g. CAT(0),
automatic, ...) groups where the conjecture of Q 1.16, `lim_{n → ∞} rank(Gⁿ) = ∞`, fails.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import WantedExt.Geometry.CATZeroSpaceShared

@[expose] public section

namespace MathlibExt.GroupTheory.CATZeroGroupBoundedPowerRankAMR10Problem0117Wanted

/-!
Source: M. Bestvina, Questions in Geometric Group Theory (updated July 2004), Q 1.17 (Dani Wise),
https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf. UnsolvedMath record UM-01100117
(`AMR-010-0117`), dataset ulamai/UnsolvedMath v1.8.0.

`rank(Gⁿ)` is the least number of generators of the direct power `Gⁿ = Fin n → G`; since it is
non-decreasing in `n`, the conjecture fails exactly when it is bounded. A CAT(0) group acts by
isometries (`IsIsometricSMul`), properly discontinuously (`ProperlyDiscontinuousSMul`) and
cocompactly on a proper CAT(0) space, CAT(0) (`IsCATZero`, `WantedExt.Geometry.CATZeroSpaceShared`,
shared with Q 2.18) being a nonempty geodesic space with the Berg–Nikolaev four-point condition
(`IsCAT0FourPoint`, MathlibExt); for empty `X` every condition on the action would hold vacuously.
`G` must be nontrivial: the trivial group would satisfy the bound vacuously. The open-ended "find"
and the other notions of niceness (automatic) are not formalized; the target is the existence of a
CAT(0) example.
-/

open MathlibExt.Geometry.CATZeroSpaceShared

/-- Wise's question (Bestvina Q 1.17), existence part: some nontrivial group `G` acting
geometrically on a proper CAT(0) space `X` (by isometries, `IsIsometricSMul`; properly
discontinuously, `ProperlyDiscontinuousSMul`; and cocompactly) has `rank(Gⁿ)` bounded independently
of `n`, so the conjecture `rank(Gⁿ) → ∞` of Q 1.16 fails for it. -/
def catZeroGroupWithBoundedPowerRank : Prop :=
  ∃ (G : Type) (_ : Group G) (X : Type) (_ : MetricSpace X) (_ : ProperSpace X)
      (_ : MulAction G X),
    IsCATZero X ∧ IsIsometricSMul G X ∧ ProperlyDiscontinuousSMul G X ∧
      (∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ g : G, x ∈ (fun y => g • y) '' K) ∧ Nontrivial G ∧
      ∃ C : ℕ, ∀ n : ℕ, ∃ s : Finset (Fin n → G),
        s.card ≤ C ∧ Subgroup.closure (s : Set (Fin n → G)) = ⊤

/--
Resolved true: the Burger–Mozes groups are infinite simple fundamental groups of compact
non-positively curved square complexes, so they act freely, cocompactly and by isometries on the
CAT(0) universal cover (a product of two trees); Bridson (Section 3.2, from Wiegold–Wilson) records
that `d(Γⁿ) ≤ d(Γ) + 1` for all `n`, so `rank(Γⁿ)` stays bounded and the conjecture of Q 1.16 fails
for these CAT(0) groups. Source: M. Bestvina, Questions in Geometric Group Theory (updated July
2004), Q 1.17 (Dani Wise), https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf;
resolution: M. R. Bridson, Concise presentations of direct products, Proc. Amer. Math. Soc. 150
(2022), no. 4, 1361-1368, arXiv:1710.05904; M. Burger and S. Mozes, Lattices in product of trees,
Publ. Math. IHÉS 92 (2000); J. Wiegold and J. S. Wilson, Growth sequences of finitely generated
groups, Arch. Math. 30 (1978), Bridson, Section 3.2 (Infinite simple groups): the Burger–Mozes
groups Γ = π₁X (X a compact non-positively curved square complex) are infinite simple, and by
Theorem 1.1(2),(5) Γⁿ has a finite presentation with at most d(Γ) + 1 generators for all n,
https://arxiv.org/abs/1710.05904.
-/
public theorem_wanted catZeroGroupWithBoundedPowerRank_holds : catZeroGroupWithBoundedPowerRank

end MathlibExt.GroupTheory.CATZeroGroupBoundedPowerRankAMR10Problem0117Wanted
