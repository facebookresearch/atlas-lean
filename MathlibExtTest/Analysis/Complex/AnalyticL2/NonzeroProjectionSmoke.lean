/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Analysis.Complex.AnalyticL2.BergmanProjection
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# A nonzero analytic L² class and its Bergman projection

The unit disk has finite positive planar area. Its constant analytic
representative `i` therefore defines a genuinely nonzero class for planar
volume restricted to that disk. The Bergman projection fixes every member
of the analytic submodule, fixes this class with positive norm, and respects
its complex scalar action.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MathlibExtTest.AnalyticL2Projection

private def disk : Set ℂ := Metric.ball 0 1

private theorem disk_measure_lt_top :
    (volume.restrict disk : Measure ℂ) Set.univ < ∞ := by
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, disk, Complex.volume_ball]
  simp

private theorem disk_measure_ne_zero : (volume : Measure ℂ) disk ≠ 0 := by
  have hp : 0 < (volume : Measure ℂ) disk := by
    rw [disk, Complex.volume_ball]
    simpa only [ENNReal.ofReal_one, one_pow, one_mul] using
      (ENNReal.coe_pos.mpr NNReal.pi_pos)
  exact hp.ne'

private theorem constant_memLp :
    MemLp (fun _ : ℂ => Complex.I) 2 (volume.restrict disk) :=
  (memLp_const_iff (by norm_num) (by norm_num)).mpr (Or.inr disk_measure_lt_top)

private def constantVector : Lp ℂ 2 (volume.restrict disk) :=
  constant_memLp.toLp (fun _ => Complex.I)

private abbrev Bergman := AnalyticL2.submodule disk (volume.restrict disk)

private theorem constantVector_mem : constantVector ∈ Bergman := by
  apply (AnalyticL2.mem_submodule_iff disk (volume.restrict disk) constantVector).mpr
  exact ⟨fun _ => Complex.I, analyticOn_const, constant_memLp.coeFn_toLp⟩

private theorem constantVector_ne_zero : constantVector ≠ 0 := by
  intro h
  have hrep : constantVector =ᵐ[volume.restrict disk] fun _ : ℂ => Complex.I :=
    constant_memLp.coeFn_toLp
  have hzero : ∀ᵐ z ∂volume.restrict disk, Complex.I = 0 := by
    filter_upwards [hrep, Lp.coeFn_zero ℂ 2 (volume.restrict disk)] with z hz hz0
    rw [h] at hz
    exact hz.symm.trans hz0
  have hm := ae_iff.mp hzero
  simp only [Complex.I_ne_zero, not_false_eq_true, Set.ofPred_true] at hm
  apply disk_measure_ne_zero
  simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using hm

private def analyticConstant : Bergman := ⟨constantVector, constantVector_mem⟩

private instance : CompleteSpace Bergman :=
  AnalyticL2.completeSpace disk Metric.isOpen_ball

private theorem projection_fixes (f : Bergman) :
    AnalyticL2.projection disk Metric.isOpen_ball (f : Lp ℂ 2 (volume.restrict disk)) = f := by
  change Bergman.orthogonalProjectionOnto (f : Lp ℂ 2 (volume.restrict disk)) = f
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self f

example : constantVector ∈ Bergman ∧ constantVector ≠ 0 :=
  ⟨constantVector_mem, constantVector_ne_zero⟩

example (f : Bergman) :
    AnalyticL2.projection disk Metric.isOpen_ball (f : Lp ℂ 2 (volume.restrict disk)) = f :=
  projection_fixes f

example :
    AnalyticL2.projection disk Metric.isOpen_ball constantVector = analyticConstant ∧
      0 < ‖AnalyticL2.projection disk Metric.isOpen_ball constantVector‖ := by
  have hfix : AnalyticL2.projection disk Metric.isOpen_ball constantVector = analyticConstant :=
    projection_fixes analyticConstant
  have hpos : 0 < ‖analyticConstant‖ := by
    change 0 < ‖constantVector‖
    exact norm_pos_iff.mpr constantVector_ne_zero
  exact ⟨hfix, hfix.symm ▸ hpos⟩

example :
    AnalyticL2.projection disk Metric.isOpen_ball (Complex.I • constantVector) =
      Complex.I • analyticConstant := by
  rw [map_smul]
  exact congrArg (fun f : Bergman => Complex.I • f) (projection_fixes analyticConstant)

end MathlibExtTest.AnalyticL2Projection
