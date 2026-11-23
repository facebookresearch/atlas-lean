/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Minimal spherical area of univalent images of the disc (Hayman–Lingham Problem 6.78)

W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Problem 6.78 (Y. Avci): for `f
∈ S`, what is the minimal spherical area of the stereographic image of `f(𝔻)`, and what is the
extremal function?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import WantedExt.Analysis.UnivalentClassSShared

@[expose] public section

namespace MathlibExt.Analysis.MinimalSphericalAreaUnivalentAMR22Problem6078Wanted

/-!
Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary
Edition (2019), arXiv:1809.07200, Problem 6.78 (Y. Avci). UnsolvedMath record UM-02306078
(`AMR-022-6078`), dataset ulamai/UnsolvedMath v1.8.0.

Spherical area is on the unit sphere (total area `4π`): `∫_E 4 / (1 + |w|²)²`, so the unit disc has
area `2π`, half the sphere. The answer is stated as: every `f ∈ S` has area at least `2π`, with
equality exactly for `f(z) = z`.
-/

/-- The spherical area of `E ⊆ ℂ` on the unit sphere (total area `4π`) under stereographic
projection: the integral of `4 / (1 + |w| ^ 2) ^ 2` over `E`. -/
noncomputable def sphericalArea (E : Set ℂ) : ℝ :=
  ∫ w in E, 4 / (1 + ‖w‖ ^ 2) ^ 2

/-- Compatibility forward for the class `S` predicate, now shared as
`UnivalentClassSShared.IsNormalizedUnivalent`. For new code, use that directly. -/
@[deprecated "Use `MathlibExt.Analysis.UnivalentClassSShared.IsNormalizedUnivalent` instead."
  (since := "2026-10-23")]
abbrev IsNormalizedUnivalent (f : ℂ → ℂ) : Prop :=
  UnivalentClassSShared.IsNormalizedUnivalent f

/-- Hayman–Lingham Problem 6.78 (Y. Avci), answered: the minimum over `f ∈ S` of the spherical
area of `f(𝔻)` is `2π` (half the sphere), attained only by `f(z) = z`. -/
def minimalSphericalAreaOfUnivalentImage : Prop :=
  ∀ f : ℂ → ℂ, UnivalentClassSShared.IsNormalizedUnivalent f →
    2 * Real.pi ≤ sphericalArea (f '' Metric.ball 0 1) ∧
      (sphericalArea (f '' Metric.ball 0 1) = 2 * Real.pi ↔ Set.EqOn f id (Metric.ball 0 1))

/--
Resolved true: Dufresnoy's lemma, stated with its equality case as Yamashita's Lemma (2.1)-(2.2),
gives `f^#(0)² ≤ β / (π - β)` (sphere of area `π`) for meromorphic `f` on `𝔻` with image of
spherical area at most `β < π`, with equality only for Möbius maps onto a spherical cap. For `f ∈
S`, `f^#(0) = 1`, so the image covers at least half the sphere, and equality forces `f(z) = z`.
Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary
Edition (2019), arXiv:1809.07200, Problem 6.78 (Y. Avci); resolution: J. Dufresnoy, Sur l'aire
sphérique décrite par les valeurs d'une fonction méromorphe, Bull. Sci. Math. 65 (1941), 214-219; S.
Yamashita, Spherical derivative of meromorphic function with image of finite spherical area, J.
Inequal. Appl. 5 (2000), 191-199, Yamashita's Lemma (2.1)-(2.2) (Dufresnoy's lemma with its equality
case): a meromorphic f on 𝔻 whose image has spherical area at most β < π (sphere of area π) has
f#(0)^2 ≤ β/(π - β), with equality only for Möbius maps onto a cap,
https://doi.org/10.1155/S1025583400000102.
-/
public theorem_wanted minimalSphericalAreaOfUnivalentImage_holds :
    minimalSphericalAreaOfUnivalentImage

end MathlibExt.Analysis.MinimalSphericalAreaUnivalentAMR22Problem6078Wanted
