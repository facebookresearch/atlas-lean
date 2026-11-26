/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Analysis.Complex.Subharmonic.Nonpositive
public import MathlibExt.Analysis.Complex.Subharmonic.RadialSlit
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# Negative subharmonic constants and finite radial slits

The constant value −1 on the complex plane satisfies all five fields of
nonpositive subharmonicity. Its normalized negative circle average is one,
whereas the constant value −∞ has infinite negative circle average.

The radial family consists of `[1/4,1/2]` and the degenerate interval
`[3/4,3/4]`. Endpoints are retained, points in the gap are excluded, and
off-axis points remain in the slit domain. An empty family removes no points.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MathlibExtTest.NonpositiveRadialSlit

private def finiteNegative : ℂ → EReal := fun _ => ((-1 : ℝ) : EReal)

private theorem angleMeasure_ne_zero :
    (volume : Measure ℝ) (Ioc 0 (2 * Real.pi)) ≠ 0 := by
  rw [Real.volume_Ioc, sub_zero]
  exact (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) Real.pi_pos)).ne'

private theorem angleMeasure_ne_top :
    (volume : Measure ℝ) (Ioc 0 (2 * Real.pi)) ≠ ∞ := by
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

private theorem finiteNegative_average (z : ℂ) (r : ℝ) :
    Complex.negativeCircleAverage finiteNegative z r = 1 := by
  unfold Complex.negativeCircleAverage
  simp only [finiteNegative, EReal.coe_neg, neg_neg, EReal.real_coe_toENNReal,
    ENNReal.ofReal_one]
  exact setLAverage_const angleMeasure_ne_zero angleMeasure_ne_top 1

private theorem finiteNegative_subharmonic :
    Complex.IsNonpositiveSubharmonicOn finiteNegative Set.univ := by
  refine ⟨isConnected_univ, ?_, ?_, ?_, ?_⟩
  · exact continuous_const.continuousOn.upperSemicontinuousOn
  · intro z hz
    exact EReal.coe_nonpos.mpr (by norm_num)
  · exact ⟨0, Set.mem_univ 0, EReal.coe_ne_bot (-1)⟩
  · intro z hz
    refine ⟨1, by norm_num, Set.subset_univ _, ?_⟩
    intro r hr hr1
    rw [finiteNegative_average]
    simpa only [finiteNegative, EReal.coe_neg, neg_neg, EReal.real_coe_toENNReal,
      ENNReal.ofReal_one] using (le_refl (1 : ℝ≥0∞))

example :
    Complex.IsNonpositiveSubharmonicOn finiteNegative Set.univ ∧
      finiteNegative 0 ≠ 0 ∧ Complex.negativeCircleAverage finiteNegative 0 (1 / 2) = 1 := by
  refine ⟨finiteNegative_subharmonic, ?_, finiteNegative_average 0 (1 / 2)⟩
  norm_num [finiteNegative]

example (z : ℂ) : finiteNegative z < ⊤ :=
  finiteNegative_subharmonic.lt_top (Set.mem_univ z)

example (z : ℂ) (r : ℝ) :
    Complex.negativeCircleAverage (fun _ => (⊥ : EReal)) z r = ∞ := by
  unfold Complex.negativeCircleAverage
  simp only [EReal.neg_bot, EReal.toENNReal_top]
  exact setLAverage_const angleMeasure_ne_zero angleMeasure_ne_top ∞

private def slits : Complex.RadialSlitData 2 where
  inner i := if i = 0 then 1 / 4 else 3 / 4
  outer i := if i = 0 then 1 / 2 else 3 / 4
  inner_nonneg i := by fin_cases i <;> norm_num
  inner_le_outer i := by fin_cases i <;> norm_num
  outer_le_one i := by fin_cases i <;> norm_num

example :
    (1 / 4 : ℝ) ∈ slits.radiusSet ∧ (1 / 2 : ℝ) ∈ slits.radiusSet ∧
      (3 / 4 : ℝ) ∈ slits.radiusSet ∧ (2 / 3 : ℝ) ∉ slits.radiusSet := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact slits.mem_radiusSet.mpr ⟨0, by norm_num [slits]⟩
  · exact slits.mem_radiusSet.mpr ⟨0, by norm_num [slits]⟩
  · exact slits.mem_radiusSet.mpr ⟨1, by norm_num [slits]⟩
  · intro h
    obtain ⟨i, hi⟩ := slits.mem_radiusSet.mp h
    fin_cases i <;> norm_num [slits] at hi

example :
    (1 / 3 : ℂ) ∉ slits.slitDomain ∧ Complex.I / 2 ∈ slits.slitDomain := by
  constructor
  · intro h
    have hn := (slits.mem_slitDomain.mp h).2
    apply hn
    apply slits.mem_slitSet.mpr
    refine ⟨slits.mem_radiusSet.mpr ⟨0, ?_⟩, ?_⟩ <;> norm_num [slits]
  · apply slits.mem_slitDomain.mpr
    constructor
    · norm_num [norm_div]
    · intro h
      have hi := (slits.mem_slitSet.mp h).2
      norm_num at hi

private def emptySlits : Complex.RadialSlitData 0 where
  inner := Fin.elim0
  outer := Fin.elim0
  inner_nonneg i := Fin.elim0 i
  inner_le_outer i := Fin.elim0 i
  outer_le_one i := Fin.elim0 i

example : emptySlits.slitDomain = Metric.ball (0 : ℂ) 1 := by
  ext z
  rw [emptySlits.mem_slitDomain, emptySlits.mem_slitSet, emptySlits.mem_radiusSet]
  simp [Metric.mem_ball, dist_zero_right]

end MathlibExtTest.NonpositiveRadialSlit
