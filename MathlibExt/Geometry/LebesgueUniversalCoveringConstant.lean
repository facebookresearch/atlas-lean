/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Lebesgue's universal covering constant and its disk lower bound

A universal convex cover is a nonempty convex set in the Euclidean plane that contains a congruent
copy, reflections allowed, of every nonempty convex planar set of diameter $1$. Lebesgue's universal
covering constant `lebesgueUniversalCoveringConstant` is the infimum, taken in $[0, \infty]$, of the
areas of the universal convex covers.

The main result, `trivialUnitDiskLowerBound_holds`, is the disk lower bound: the constant is at
least $\pi/4$.

## Proof

A closed disk of radius $1/2$ is a nonempty convex set of diameter $1$, so every universal convex
cover contains its image under some isometry of the plane. That image is again a closed disk of
radius $1/2$, of area $\pi/4$, so every universal convex cover has area at least $\pi/4$.

## Implementation notes

The definitions and the theorem keep the full names they had in the wanted module
`WantedExt/Geometry/LebesgueUniversalCoveringConstantWanted.lean`, which imports this module and
states further results on the constant with these definitions; this is why the namespace ends in
`Wanted`.

## References

* John C. Baez, Karine Bagdasaryan and Philip Gibbs, *The Lebesgue universal covering problem*,
  J. Comput. Geom. 6 (2015), 288-299, arXiv:1502.01251, Section 1: universal coverings and the
  history of the problem.
-/

open MeasureTheory

namespace MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted

@[expose] public noncomputable section

/-- **The Euclidean plane of Lebesgue's covering problem.** The ambient space is the Euclidean
plane $\mathbb{R}^2$, with the Euclidean distance. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- **Convex sets of diameter one.** A set $K$ in the Euclidean plane $\mathbb{R}^2$ is a
unit-diameter convex set when it is nonempty and convex and its diameter
$\sup_{x, y \in K} \lVert x - y \rVert$ is exactly $1$. -/
def IsUnitDiameterConvexSet (K : Set Plane) : Prop :=
  K.Nonempty ∧ Convex ℝ K ∧ Metric.diam K = 1

/-- **Covering a congruent copy.** A planar set $\Omega$ covers a congruent copy of a planar set
$K$ when some isometry $e$ of the plane onto itself satisfies $e(K) \subseteq \Omega$.

Isometries include reflections. -/
def CoversCongruentCopy (Ω K : Set Plane) : Prop :=
  ∃ e : Plane ≃ᵢ Plane, e '' K ⊆ Ω

/-- **Universal convex covers.** A set $\Omega$ in the Euclidean plane $\mathbb{R}^2$ is a universal
convex cover when it is nonempty and convex and, for every nonempty convex set
$K \subseteq \mathbb{R}^2$ of diameter $1$, some isometry $e$ of the plane onto itself satisfies
$e(K) \subseteq \Omega$. -/
def IsUniversalConvexCover (Ω : Set Plane) : Prop :=
  Ω.Nonempty ∧ Convex ℝ Ω ∧
    ∀ K : Set Plane, IsUnitDiameterConvexSet K → CoversCongruentCopy Ω K

/-- **Planar area.** The area of a set $S$ in the Euclidean plane $\mathbb{R}^2$
is its Lebesgue measure (outer measure if $S$ is not measurable), a value in $[0, \infty]$,
so infinite area is allowed. -/
def planarArea (S : Set Plane) : ENNReal :=
  volume S

/-- **Areas of universal convex covers.** The set of admissible cover areas is the set of all
$a \in [0, \infty]$ for which there is a universal convex cover $\Omega$ in the plane (a nonempty
convex set containing a congruent copy of every nonempty convex planar set of diameter $1$) whose
Lebesgue area is $a$. -/
def admissibleCoverAreas : Set ENNReal :=
  {a | ∃ Ω : Set Plane, IsUniversalConvexCover Ω ∧ planarArea Ω = a}

/--
**Lebesgue universal covering constant.** Call a set $\Omega$ in the Euclidean plane
$\mathbb{R}^2$ a universal convex cover if it is nonempty and convex and, for every nonempty
convex set $K \subseteq \mathbb{R}^2$ of diameter exactly $1$, some isometry of the plane onto
itself maps $K$ into $\Omega$. The Lebesgue universal covering constant is the infimum, taken in
$[0, \infty]$, of the Lebesgue areas of all universal convex covers; the infimum of an empty
family would be $\infty$.

The definition does not assume that a universal convex cover of minimal area exists.
-/
def lebesgueUniversalCoveringConstant : ENNReal :=
  sInf admissibleCoverAreas

/-- **Disk lower bound for Lebesgue's universal covering constant (statement).** The proposition
that Lebesgue's universal covering constant is at least $\pi/4$.

This is the bound given by a disk of radius $1/2$, which has diameter $1$ and area $\pi/4$. -/
def trivialUnitDiskLowerBound : Prop :=
  ENNReal.ofReal (Real.pi / 4) ≤ lebesgueUniversalCoveringConstant

/-- A closed disk of radius $1/2$ is a nonempty convex set of diameter $1$. -/
private theorem isUnitDiameterConvexSet_closedBall (x : Plane) :
    IsUnitDiameterConvexSet (Metric.closedBall x (1 / 2)) := by
  refine ⟨Metric.nonempty_closedBall.2 (by norm_num), convex_closedBall x _, ?_⟩
  rw [Metric.diam_closedBall_eq x (by norm_num)]
  norm_num

/-- A closed disk of radius $1/2$ has area $\pi/4$. -/
private theorem planarArea_closedBall (x : Plane) :
    planarArea (Metric.closedBall x (1 / 2)) = ENNReal.ofReal (Real.pi / 4) := by
  rw [planarArea, EuclideanSpace.volume_closedBall_fin_two, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- Every universal convex cover has area at least $\pi/4$: it contains an isometric image of a
closed disk of radius $1/2$, which is again such a disk. -/
private theorem ofReal_pi_div_four_le_planarArea {Ω : Set Plane} (hΩ : IsUniversalConvexCover Ω) :
    ENNReal.ofReal (Real.pi / 4) ≤ planarArea Ω := by
  obtain ⟨e, he⟩ := hΩ.2.2 _ (isUnitDiameterConvexSet_closedBall 0)
  rw [← planarArea_closedBall (e 0), ← IsometryEquiv.image_closedBall]
  exact measure_mono he

/-- **Disk lower bound for Lebesgue's universal covering constant.** Lebesgue's universal covering
constant, the infimum of the areas of the nonempty convex planar sets that contain a congruent
copy of every nonempty convex planar set of diameter $1$, is at least $\pi/4$, the area of a disk
of radius $1/2$.

Source: Radius-half disk lower-bound row, optimization catalogue constant 13b. -/
theorem trivialUnitDiskLowerBound_holds : trivialUnitDiskLowerBound :=
  le_sInf fun _ ⟨_, hΩ, hΩa⟩ => hΩa ▸ ofReal_pi_div_four_le_planarArea hΩ

end

end MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted
