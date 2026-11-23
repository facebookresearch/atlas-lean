/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cover-decomposability of planar convex sets (Oberwolfach Reports 44/2008)

Oberwolfach workshop Discrete Geometry (2008), G. Tóth (with D. Pálvölgyi), Pach's conjecture: every
planar convex set `P` is cover-decomposable, i.e. for some `k` every `k`-fold covering of the plane
by translates of `P` splits into two coverings.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MathlibExt.Geometry.ConvexCoverDecomposabilityOWR2090Problem017Wanted

/-!
Source: G. Tóth (with D. Pálvölgyi), in Discrete Geometry, Oberwolfach Reports 5 (2008), no. 44, pp.
2533-2534, Conjecture (J. Pach), DOI 10.4171/OWR/2008/44. UnsolvedMath record UM-30001064
(`OWR-2090-017`), dataset ulamai/UnsolvedMath v1.8.0.

A covering is an indexed family of translates `P + t_i` (repetitions allowed, any index type in
`Type`); `k`-fold means every point lies in at least `k` members counted by index; it splits into
two coverings if some set of indices and its complement both cover the plane. The source's Theorem
A(ii) lists the open unit disc as cover-decomposable after an unpublished manuscript of
Mani-Levitska and Pach; Pach and Pálvölgyi later proved the opposite.
-/

/-- The Euclidean plane. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- The translates `P + t i` (`i ∈ ι`) form a `k`-fold covering of the plane: every point lies in
at least `k` of them, counted by index. -/
def IsMultipleCovering (P : Set Plane) (k : ℕ) {ι : Type} (t : ι → Plane) : Prop :=
  ∀ x : Plane, (k : ℕ∞) ≤ {i | x - t i ∈ P}.encard

/-- The translates `P + t i` with `i ∈ s` cover the plane. -/
def CoversPlane (P : Set Plane) {ι : Type} (t : ι → Plane) (s : Set ι) : Prop :=
  ∀ x : Plane, ∃ i ∈ s, x - t i ∈ P

/-- `P` is cover-decomposable: for some `k`, every `k`-fold covering of the plane by translates of
`P` splits into two coverings. -/
def IsCoverDecomposable (P : Set Plane) : Prop :=
  ∃ k : ℕ, ∀ (ι : Type) (t : ι → Plane), IsMultipleCovering P k t →
    ∃ s : Set ι, CoversPlane P t s ∧ CoversPlane P t sᶜ

/-- Pach's conjecture (Oberwolfach Report 44/2008, pp. 2533-2534): every planar convex set is
cover-decomposable. -/
def convexCoverDecomposable : Prop :=
  ∀ P : Set Plane, Convex ℝ P → IsCoverDecomposable P

/--
Resolved false: Pach and Pálvölgyi proved (Theorem 2) that for every `m` some `m`-fold covering of
the plane by open unit disks cannot be split into two coverings, so the open unit disk, a convex
set, is not cover-decomposable. Source: G. Tóth (with D. Pálvölgyi), in Discrete Geometry,
Oberwolfach Reports 5 (2008), no. 44, pp. 2533-2534, Conjecture (J. Pach), DOI 10.4171/OWR/2008/44;
resolution: J. Pach and D. Pálvölgyi, Unsplittable coverings in the plane, Adv. Math. 302 (2016),
arXiv:1310.6900, Theorem 2: for every positive integer m there is an m-fold covering of the plane
with open unit disks that cannot be split into 2 coverings; Theorem 3 extends this to open convex
sets with positive curvature at the tangency points of two parallel supporting lines,
https://arxiv.org/abs/1310.6900.
-/
public theorem_wanted convexCoverDecomposable_refuted : ¬ convexCoverDecomposable

end MathlibExt.Geometry.ConvexCoverDecomposabilityOWR2090Problem017Wanted
