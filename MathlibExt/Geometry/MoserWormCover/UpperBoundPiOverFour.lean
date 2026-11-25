/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.MoserWormCover
public import MathlibExt.Geometry.MoserWormCover.HalfDisk

/-!
# The convex worm cover constant is at most π/4

The closed disk `halfDisk` of radius `1/2` is a convex universal cover of unit
arcs, and its area is `π/4`. Hence the convex worm cover constant, the infimum
of the areas of convex universal covers, is at most `π/4`.

## Main statements

* `MoserConvexWormCoverConstant.upperBoundPiOverFour`: the claim that the
  convex worm cover constant is at most `π/4`.
* `MoserConvexWormCoverConstant.upperBoundPiOverFour_holds`: the claim holds.
-/

@[expose] public section

open MeasureTheory Set

namespace MoserConvexWormCoverConstant

/-- **Proposition: the convex worm cover constant is at most π/4.** A unit arc is a
continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$. The convex worm cover
constant is the infimum of the areas of the nonempty convex sets $\Omega \subseteq \mathbb{C}$
that contain, for every unit arc $\gamma$, the image of $\gamma$ under some rotation followed by
a translation. This proposition states that the convex worm cover constant is at most $\pi/4$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def upperBoundPiOverFour : Prop := convexWormCoverConstant ≤ Real.pi / 4

/-- **Covers give upper bounds on the convex worm cover constant.** Let $r \ge 0$ be a real
number. If some set $\Omega \subseteq \mathbb{C}$ is a convex universal cover of unit arcs
whose Lebesgue measure is at most $r$, then the convex worm cover constant is at most $r. -/
private theorem convexUpperBound_of_cover {r : ℝ} (hr : 0 ≤ r)
    (h : ∃ Ω : Set ℂ, IsConvexUniversalCover Ω ∧ volume Ω ≤ ENNReal.ofReal r) :
    convexWormCoverConstant ≤ r := by
  rcases h with ⟨Ω, hΩ, harea⟩
  have hi : convexCoverAreaInfimum ≤ ENNReal.ofReal r :=
    (sInf_le (s := convexCoverAreas) ⟨Ω, hΩ, rfl⟩).trans harea
  have hreal := ENNReal.toReal_mono (by simp : ENNReal.ofReal r ≠ ⊤) hi
  simpa [convexWormCoverConstant, ENNReal.toReal_ofReal hr] using hreal

/-- The disk of diameter one is the closed ball of radius `1/2` centred at `0`. -/
private theorem halfDisk_eq_closedBall :
    halfDisk = Metric.closedBall (0 : ℂ) (1 / 2 : ℝ) := by
  ext z
  simp [halfDisk, Metric.mem_closedBall, dist_eq_norm]

/-- **The disk of diameter one is a convex universal cover.** The closed disk
$\{z \in \mathbb{C} : |z| \le 1/2\}$ is nonempty, convex, and covers every unit arc. -/
theorem halfDisk_isConvexUniversalCover : IsConvexUniversalCover halfDisk := by
  refine ⟨⟨0, by simp [halfDisk]⟩, ?_, halfDiskCovers_holds⟩
  rw [halfDisk_eq_closedBall]
  exact convex_closedBall _ _

/-- **The area of the disk of diameter one is π/4.** The Lebesgue measure of the closed
disk $\{z \in \mathbb{C} : |z| \le 1/2\}$ is $\pi/4$. -/
theorem halfDisk_volume : volume halfDisk = ENNReal.ofReal (Real.pi / 4) := by
  have hpi : (NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi := by
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  rw [halfDisk_eq_closedBall, Complex.volume_closedBall, hpi,
    ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 2)]
  congr 1
  ring

/-- **The convex worm cover constant is at most π/4.** A unit arc is a continuous
curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$. The convex worm cover constant,
the infimum of the areas of the nonempty convex sets $\Omega \subseteq \mathbb{C}$ that contain,
for every unit arc $\gamma$, the image of $\gamma$ under some rotation followed by a translation,
is at most $\pi/4$.

Source: Optimization Problems, constant 13a, closed claim `upperBoundPiOverFour`.
-/
theorem upperBoundPiOverFour_holds : upperBoundPiOverFour :=
  convexUpperBound_of_cover (by positivity) ⟨halfDisk, halfDisk_isConvexUniversalCover,
    halfDisk_volume.le⟩

end MoserConvexWormCoverConstant
