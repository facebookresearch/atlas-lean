/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.LebesgueUniversalCoveringConstant
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import MathlibExt.Geometry.Euclidean.Jung

/-!
# Jung's upper bound for Lebesgue's universal covering constant

Jung's theorem in dimension two gives a universal covering disk of area $\pi/3$, yielding
`trivialJungElekes1994UpperBound_holds`.
-/

namespace MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted

@[expose] public noncomputable section

/-- **Jung's upper bound for Lebesgue's universal covering constant (statement).** The proposition
that Lebesgue's universal covering constant is at most $\pi/3$.

This is the bound given by Jung's theorem: a closed disk of radius $1/\sqrt{3}$, of area $\pi/3$,
contains a translate of every planar set of diameter $1$. -/
def trivialJungElekes1994UpperBound : Prop :=
  lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal (Real.pi / 3)

/-- Translating the center of a Jung disk to the origin puts each set in the same disk. -/
private theorem isUniversalConvexCover_jungDisk :
    IsUniversalConvexCover (Metric.closedBall (0 : Plane) (Real.sqrt (1 / 3))) := by
  refine ⟨Metric.nonempty_closedBall.2 (Real.sqrt_nonneg _), convex_closedBall _ _, ?_⟩
  rintro K ⟨_, _, hdiam⟩
  have hbounded : Bornology.IsBounded K := by
    by_contra h
    exact zero_ne_one ((Metric.diam_eq_zero_of_unbounded h).symm.trans hdiam)
  obtain ⟨c, hc⟩ := Euclidean.JungWanted.jung (by decide : 0 < 2) K hbounded
  rw [Nat.cast_ofNat, hdiam, mul_one, show (2 : ℝ) / (2 * (2 + 1)) = 1 / 3 by norm_num] at hc
  refine ⟨IsometryEquiv.subRight c, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [IsometryEquiv.subRight_apply, Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm]
  exact hc hx

/-- **Jung's bound for the Lebesgue covering problem.** The Lebesgue universal covering constant
is at most $\pi/3$.

Source: Jung's theorem, quoted in Elekes (1994), catalogue constant 13b. -/
theorem trivialJungElekes1994UpperBound_holds : trivialJungElekes1994UpperBound := by
  refine sInf_le ⟨_, isUniversalConvexCover_jungDisk, ?_⟩
  rw [planarArea, EuclideanSpace.volume_closedBall_fin_two,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

end

end MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted
