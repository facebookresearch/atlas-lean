/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Almost geodesic completeness of cocompact CAT(0) spaces (Bestvina, Q 2.18)

M. Bestvina, Questions in Geometric Group Theory, Q 2.18 (Ross Geoghegan): a proper CAT(0) space `M`
is almost geodesically complete if there is `R ≥ 0` such that for all `a, b ∈ M` some infinite
geodesic ray from `a` passes within `R` of `b`. If `Isom(M)` acts cocompactly on `M`, is `M` almost
geodesically complete?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Geometry.CATZeroSpaceShared

@[expose] public section

namespace MathlibExt.Geometry.CocompactCATZeroAlmostGeodesicallyCompleteAMR10Problem0218Wanted

/-!
Source: M. Bestvina, Questions in Geometric Group Theory (updated July 2004), Q 2.18 (Ross
Geoghegan), https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf. UnsolvedMath record
UM-01100218 (`AMR-010-0218`), dataset ulamai/UnsolvedMath v1.8.0.

CAT(0) (`IsCATZero`, `WantedExt.Geometry.CATZeroSpaceShared`, shared with Q 1.17) is a nonempty
geodesic space with the Berg–Nikolaev four-point condition (`IsCAT0FourPoint`, MathlibExt), which
characterizes CAT(0) among geodesic spaces. `Isom(M)` acts cocompactly when the isometric images of
one compact set cover `M`. `M` is assumed non-compact, as in Geoghegan–Ontaneda: a compact space (a
point) has no geodesic rays, so the question is about non-compact `M`.
-/

open MathlibExt.Geometry.CATZeroSpaceShared

/-- `γ` is a geodesic ray from `a`: `γ 0 = a` and `γ` is an isometric embedding of `[0, ∞)`. -/
def IsGeodesicRayFrom {X : Type*} [MetricSpace X] (γ : ℝ → X) (a : X) : Prop :=
  γ 0 = a ∧ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → dist (γ s) (γ t) = |s - t|

/-- `X` is almost geodesically complete: there is `R ≥ 0` such that for all `a`, `b` some geodesic
ray from `a` passes within `R` of `b`. -/
def IsAlmostGeodesicallyComplete (X : Type*) [MetricSpace X] : Prop :=
  ∃ R : ℝ, 0 ≤ R ∧ ∀ a b : X, ∃ γ : ℝ → X, IsGeodesicRayFrom γ a ∧
    ∃ t : ℝ, 0 ≤ t ∧ dist (γ t) b ≤ R

/-- `Isom(X)` acts cocompactly: some compact `K` has `⋃_{g ∈ Isom(X)} g K = X`. -/
def IsIsometryCocompact (X : Type*) [MetricSpace X] : Prop :=
  ∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ g : X ≃ᵢ X, x ∈ g '' K

/-- Geoghegan's question (Bestvina Q 2.18), answered: every non-compact proper CAT(0) space on
which `Isom(X)` acts cocompactly is almost geodesically complete. -/
def cocompactCATZeroAlmostGeodesicallyComplete : Prop :=
  ∀ (X : Type) [MetricSpace X] [ProperSpace X], IsCATZero X → ¬ CompactSpace X →
    IsIsometryCocompact X → IsAlmostGeodesicallyComplete X

/--
Resolved true: Geoghegan and Ontaneda proved that every non-compact proper CAT(0) space on which the
full isometry group acts cocompactly is almost geodesically complete (Ontaneda had the case of a
cocompact group with discrete orbits). Source: M. Bestvina, Questions in Geometric Group Theory
(updated July 2004), Q 2.18 (Ross Geoghegan),
https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf; resolution: R. Geoghegan and P.
Ontaneda, Boundaries of cocompact proper CAT(0) spaces, Topology 46 (2007), 129-137,
arXiv:math/0407506 (as 'Cocompact proper CAT(0) spaces'), Theorem 5: "Every non-compact cocompact
proper CAT(0) space is almost geodesically complete" (cocompact: a compact generating domain for the
full isometry group), from Theorem 1 and Ontaneda's Theorem A, https://arxiv.org/abs/math/0407506.
-/
public theorem_wanted cocompactCATZeroAlmostGeodesicallyComplete_holds :
    cocompactCATZeroAlmostGeodesicallyComplete

end MathlibExt.Geometry.CocompactCATZeroAlmostGeodesicallyCompleteAMR10Problem0218Wanted
