/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Products of caustic-cut segment lengths of even N-periodics in the elliptic billiard (k₁₁₇)

Reznik, Garcia and Koiller, Eighty New Invariants of N-Periodics in the Elliptic Billiard, Table 2,
invariant `k₁₁₇`: for even `N`, the products `∏ l_i` and `∏ r_i` are invariant over the Poncelet
family of `N`-periodic billiard orbits in an ellipse tangent to a fixed confocal caustic, where the
caustic contact point `P''_i` of the side `P_i P_{i+1}` cuts it into `l_i = |P''_i - P_i|` and `r_i
= |P_{i+1} - P''_i|`.
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Dynamics.EllipticBilliardPonceletShared

@[expose] public section

namespace MathlibExt.Dynamics.EllipticBilliardEvenSegmentProductsAMR50Problem0008Wanted

/-!
Source: D. Reznik, R. Garcia and J. Koiller, Eighty New Invariants of N-Periodics in the Elliptic
Billiard, arXiv:2004.12497v11 (2020; Arnold Math. J. 7 (2021), 341-355), Table 2, invariant k₁₁₇.
UnsolvedMath record UM-05100008 (`AMR-050-0008`), dataset ulamai/UnsolvedMath v1.8.0.

The table is the ellipse `x²/a² + y²/b² = 1`, `0 < b < a`, in standard position (the invariant is
unchanged by isometries); the caustic is the confocal ellipse `x²/(a² - λ) + y²/(b² - λ) = 1`, `0 <
λ < b²`; the Poncelet family is the set of `N`-periodic orbits with turning number one
(`PonceletOrbit a b λ N` of `WantedExt/Dynamics/EllipticBilliardPonceletShared.lean`: vertices `(a
cos tᵢ, b sin tᵢ)` with `t` strictly increasing and `t (i + N) = t i + 2π`, every side touching the
caustic at an interior point `P''_i`). `l_i = |P''_i - P_i|`, `r_i = |P_{i+1} - P''_i|`, sums and
products over one period `i < N`. `N ≥ 3` excludes the degenerate two-periodic orbits along the
axes. Stachel writes `r_i = |Q_{i-1} P_i|`, which is `r_{i-1}` here; the products over a period are
the same. Only turning number one is formalized (the family the source computes); Stachel's theorem
also covers self-intersecting orbits. Numerically `∏ l_i = ∏ r_i = λ^{N/2}` on every family checked
(`a/b ∈ {1.1, 1.5, 2, 3}`, even `N ≤ 12`, eight orbits each, relative spread below `1e-13`).
-/

open MathlibExt.Dynamics.EllipticBilliardPonceletShared

/-- Reznik–Garcia–Koiller, invariant `k₁₁₇`: for even `N`, the products `∏ l_i` and `∏ r_i` of the
segment lengths cut on the sides by the caustic contact points are the same for every orbit of the
Poncelet family of `N`-periodic orbits (turning number one) tangent to a fixed confocal elliptic
caustic. -/
def evenSegmentProductsInvariant : Prop :=
  ∀ (a b lam : ℝ) (N : ℕ), 0 < b → b < a → 0 < lam → lam < b ^ 2 → 3 ≤ N → Even N →
    ∀ O O' : PonceletOrbit a b lam N,
      ∏ i ∈ Finset.range N, O.l i = ∏ i ∈ Finset.range N, O'.l i ∧
        ∏ i ∈ Finset.range N, O.r i = ∏ i ∈ Finset.range N, O'.r i

/--
Resolved true: Stachel (Theorem 10) proves that for even `N` both products equal `k_e^{N/2}` with
`k_e` the constant of the confocal pair, so they are the same for every orbit of the family. Source:
D. Reznik, R. Garcia and J. Koiller, Eighty New Invariants of N-Periodics in the Elliptic Billiard,
arXiv:2004.12497v11 (2020; Arnold Math. J. 7 (2021), 341-355), Table 2, invariant k₁₁₇; resolution:
H. Stachel, On the motion of billiards in ellipses, Eur. J. Math. 8 (2022), 1602-1622;
arXiv:2105.03624, Theorem 10: for even N the products r_1 r_2 ⋯ r_N = l_1 l_2 ⋯ l_N = k_e^{N/2} are
invariant against billiard motions (k_e the constant of the confocal pair); introduced as the proof
of the invariance of k117 in [RGK, Table 2], via Theorem 8 (r_i r_{i+n} = l_i l_{i+n} = k_e for N =
4n, r_i l_{i+n} = l_i r_{i+n+1} = k_e for N = 4n + 2), https://doi.org/10.1007/s40879-021-00524-2.
-/
public theorem_wanted evenSegmentProductsInvariant_holds : evenSegmentProductsInvariant

end MathlibExt.Dynamics.EllipticBilliardEvenSegmentProductsAMR50Problem0008Wanted
