/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sums of caustic-cut segment lengths of odd N-periodics in the elliptic billiard (k₁₁₈)

Reznik, Garcia and Koiller, Eighty New Invariants of N-Periodics in the Elliptic Billiard, Table 2,
invariant `k₁₁₈`: for odd `N`, the sums `∑ l_i` and `∑ r_i` are invariant over the Poncelet family
of `N`-periodic billiard orbits in an ellipse tangent to a fixed confocal caustic, with common value
`L/2`, `L` the perimeter; the caustic contact point `P''_i` of the side `P_i P_{i+1}` cuts it into
`l_i = |P''_i - P_i|` and `r_i = |P_{i+1} - P''_i|`.
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Dynamics.EllipticBilliardPonceletShared

@[expose] public section

namespace MathlibExt.Dynamics.EllipticBilliardOddSegmentSumsAMR50Problem0009Wanted

/-!
Source: D. Reznik, R. Garcia and J. Koiller, Eighty New Invariants of N-Periodics in the Elliptic
Billiard, arXiv:2004.12497v11 (2020; Arnold Math. J. 7 (2021), 341-355), Table 2, invariant k₁₁₈.
UnsolvedMath record UM-05100009 (`AMR-050-0009`), dataset ulamai/UnsolvedMath v1.8.0.

The table is the ellipse `x²/a² + y²/b² = 1`, `0 < b < a`, in standard position (the invariant is
unchanged by isometries); the caustic is the confocal ellipse `x²/(a² - λ) + y²/(b² - λ) = 1`, `0 <
λ < b²`; the Poncelet family is the set of `N`-periodic orbits with turning number one
(`PonceletOrbit a b λ N` of `WantedExt/Dynamics/EllipticBilliardPonceletShared.lean`: vertices `(a
cos tᵢ, b sin tᵢ)` with `t` strictly increasing and `t (i + N) = t i + 2π`, every side touching the
caustic at an interior point `P''_i`). `l_i = |P''_i - P_i|`, `r_i = |P_{i+1} - P''_i|`, sums and
products over one period `i < N`. `N ≥ 3` excludes the degenerate two-periodic orbits along the
axes. Stachel writes `r_i = |Q_{i-1} P_i|`, which is `r_{i-1}` here; the sums over a period are the
same. Only turning number one is formalized (the family the source computes); Stachel's theorem also
covers self-intersecting orbits. Numerically `∑ l_i = ∑ r_i = L/2` on every family checked (`a/b ∈
{1.1, 1.5, 2, 3}`, odd `N ≤ 11`, eight orbits each, spread below `1e-13`).
-/

open MathlibExt.Dynamics.EllipticBilliardPonceletShared

/-- Reznik–Garcia–Koiller, invariant `k₁₁₈`: for odd `N`, the sums `∑ l_i` and `∑ r_i` of the
segment lengths cut on the sides by the caustic contact points both equal half the perimeter, and
they are the same for every orbit of the Poncelet family of `N`-periodic orbits (turning number
one) tangent to a fixed confocal elliptic caustic. -/
def oddSegmentSumsInvariant : Prop :=
  ∀ (a b lam : ℝ) (N : ℕ), 0 < b → b < a → 0 < lam → lam < b ^ 2 → 3 ≤ N → Odd N →
    (∀ O : PonceletOrbit a b lam N,
      ∑ i ∈ Finset.range N, O.l i = O.perimeter / 2 ∧
        ∑ i ∈ Finset.range N, O.r i = O.perimeter / 2) ∧
    ∀ O O' : PonceletOrbit a b lam N,
      ∑ i ∈ Finset.range N, O.l i = ∑ i ∈ Finset.range N, O'.l i ∧
        ∑ i ∈ Finset.range N, O.r i = ∑ i ∈ Finset.range N, O'.r i

/--
Resolved true: Stachel proves `∑ l_i = ∑ r_i = L/2` for every periodic billiard with odd `N`
(Theorem 4.5) and that the perimeter `L` is the same for all orbits of the family (Lemma 4.4).
Source: D. Reznik, R. Garcia and J. Koiller, Eighty New Invariants of N-Periodics in the Elliptic
Billiard, arXiv:2004.12497v11 (2020; Arnold Math. J. 7 (2021), 341-355), Table 2, invariant k₁₁₈;
resolution: H. Stachel, The geometry of billiards in ellipses and their Poncelet grids, J. Geom. 112
(2021), Paper No. 40; arXiv:2105.03362, Theorem 4.5: in each N-sided periodic billiard opposite
segments are congruent, and for odd N, Σ l_i = Σ r_i = L_e/2; Lemma 4.4: the length L_e of a
periodic N-sided billiard with an ellipse as caustic is independent of the initial vertex; Section
4.2 presents these as new proofs of the invariant k118 of [RGK, Table 2],
https://doi.org/10.1007/s00022-021-00606-2.
-/
public theorem_wanted oddSegmentSumsInvariant_holds : oddSegmentSumsInvariant

end MathlibExt.Dynamics.EllipticBilliardOddSegmentSumsAMR50Problem0009Wanted
