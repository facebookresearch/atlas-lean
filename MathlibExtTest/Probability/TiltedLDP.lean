/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.TiltedLDP

/-! Non-vacuity tests for the tilted large deviation principle: tilting the Dirac LDP. -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal
open MathlibExt.Probability.LargeDeviationPrinciple
open MathlibExt.Probability.TiltedLDP

namespace MathlibExtTest.Probability.TiltedLDP

/-- Tilting the Dirac LDP at `0` on `ℝ` by `Real.cos` gives an LDP. -/
example : SatisfiesLDP (tiltedMeasure (fun _ => Measure.dirac (0 : ℝ)) Real.cos)
    (fun x => ((⨆ y, ((Real.cos y : EReal) - (diracRate (0 : ℝ) y : EReal))) -
      ((Real.cos x : EReal) - (diracRate (0 : ℝ) x : EReal))).toENNReal) :=
  satisfiesLDP_tiltedMeasure (satisfiesLDP_dirac (0 : ℝ)) Real.continuous_cos
    Real.abs_cos_le_one

/-- Tilting the Dirac LDP at `1` on `ℝ` by a constant gives an LDP. -/
example : SatisfiesLDP (tiltedMeasure (fun _ => Measure.dirac (1 : ℝ)) (fun _ => (2 : ℝ)))
    (fun x => ((⨆ y, (((2 : ℝ) : EReal) - (diracRate (1 : ℝ) y : EReal))) -
      (((2 : ℝ) : EReal) - (diracRate (1 : ℝ) x : EReal))).toENNReal) :=
  satisfiesLDP_tiltedMeasure (satisfiesLDP_dirac (1 : ℝ)) continuous_const
    (C := 2) (fun _ => by norm_num)

/-- The tilted rate function vanishes at a maximiser of `F - I`. -/
example : ((⨆ y, ((Real.cos y : EReal) - (diracRate (0 : ℝ) y : EReal))) -
    ((Real.cos 0 : EReal) - (diracRate (0 : ℝ) 0 : EReal))).toENNReal = 0 := by
  rw [tiltedRate_eq_zero_iff]
  refine le_antisymm (le_iSup (fun y => (Real.cos y : EReal) - (diracRate (0 : ℝ) y : EReal)) 0)
    (iSup_le fun y => ?_)
  by_cases hy : y = 0
  · rw [hy]
  · rw [diracRate_apply_of_ne hy, EReal.coe_ennreal_top, diracRate_apply_self]
    simp

end MathlibExtTest.Probability.TiltedLDP
