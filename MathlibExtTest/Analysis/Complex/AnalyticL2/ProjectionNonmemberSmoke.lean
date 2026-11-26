/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Analysis.Complex.AnalyticL2.BergmanProjection
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Bergman projection of a nonanalytic step class

On the unit disk, let the representative be one on the right half-disk and
zero on the left half-disk. A continuous analytic representative would have
both values at the origin, so this L2 class lies outside the analytic
submodule. Its Bergman projection has a nonzero orthogonal residual and is
idempotent when applied again to its analytic output.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace MathlibExtTest.ProjectionNonmember

private def disk : Set ℂ := Metric.ball 0 1
private def right : Set ℂ := disk ∩ {z : ℂ | 0 < z.re}
private def left : Set ℂ := disk ∩ {z : ℂ | z.re < 0}
private theorem disk_open : IsOpen disk := Metric.isOpen_ball
private theorem right_open : IsOpen right :=
  disk_open.inter (isOpen_lt continuous_const Complex.continuous_re)
private theorem left_open : IsOpen left :=
  disk_open.inter (isOpen_lt Complex.continuous_re continuous_const)

private theorem finite_disk : (volume.restrict disk : Measure ℂ) Set.univ < ∞ := by
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, disk, Complex.volume_ball]
  simp

private def step : ℂ → ℂ := right.indicator (fun _ => 1)
private theorem step_memLp : MemLp step 2 (volume.restrict disk) := by
  have h : MemLp (fun _ : ℂ => (1 : ℂ)) 2 (volume.restrict disk) :=
    (memLp_const_iff (by norm_num) (by norm_num)).mpr (Or.inr finite_disk)
  exact h.indicator right_open.measurableSet.nullMeasurableSet
private def vector : Lp ℂ 2 (volume.restrict disk) := step_memLp.toLp step
private abbrev Bergman := AnalyticL2.submodule disk (volume.restrict disk)
private instance : CompleteSpace Bergman := AnalyticL2.completeSpace disk disk_open

private theorem zero_mem_closure_right : (0 : ℂ) ∈ closure right := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let r : ℝ := min (ε / 2) (1 / 2)
  have hr : 0 < r := lt_min (half_pos hε) (by norm_num)
  have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hr1 : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨(r : ℂ), ?_, ?_⟩
  · change (r : ℂ) ∈ disk ∧ 0 < (r : ℂ).re
    constructor
    · change dist (r : ℂ) 0 < 1
      simpa [dist_eq_norm, abs_of_pos hr] using hr1
    · simpa using hr
  · simpa [dist_eq_norm, abs_of_pos hr] using hrε

private theorem zero_mem_closure_left : (0 : ℂ) ∈ closure left := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let r : ℝ := min (ε / 2) (1 / 2)
  have hr : 0 < r := lt_min (half_pos hε) (by norm_num)
  have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hr1 : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨((-r : ℝ) : ℂ), ?_, ?_⟩
  · change ((-r : ℝ) : ℂ) ∈ disk ∧ ((-r : ℝ) : ℂ).re < 0
    constructor
    · change dist ((-r : ℝ) : ℂ) 0 < 1
      simpa [dist_eq_norm, abs_of_pos hr] using hr1
    · simpa using neg_neg_of_pos hr
  · simpa [dist_eq_norm, abs_of_pos hr] using hrε

private theorem vector_not_mem : vector ∉ Bergman := by
  intro h
  obtain ⟨g, hg, hrep⟩ := (AnalyticL2.mem_submodule_iff disk (volume.restrict disk) vector).mp h
  have hstep : g =ᵐ[volume.restrict disk] step := by
    filter_upwards [hrep, step_memLp.coeFn_toLp] with z hz hv
    exact hz.symm.trans hv
  have hright : g =ᵐ[volume.restrict right] fun _ => (1 : ℂ) := by
    have h := ae_restrict_of_ae_restrict_of_subset (show right ⊆ disk from inter_subset_left) hstep
    filter_upwards [h, ae_restrict_mem right_open.measurableSet] with z hz hzr
    exact hz.trans (indicator_of_mem hzr _)
  have hleft : g =ᵐ[volume.restrict left] fun _ => (0 : ℂ) := by
    have h := ae_restrict_of_ae_restrict_of_subset (show left ⊆ disk from inter_subset_left) hstep
    filter_upwards [h, ae_restrict_mem left_open.measurableSet] with z hz hzl
    have hnot : z ∉ right := by
      intro hzr
      have hl : z.re < 0 := hzl.2
      have hr : 0 < z.re := hzr.2
      exact (not_lt_of_ge hl.le) hr
    exact hz.trans (indicator_of_notMem hnot _)
  have gRight : EqOn g (fun _ => (1 : ℂ)) right :=
    Measure.eqOn_open_of_ae_eq hright right_open (hg.continuousOn.mono inter_subset_left) continuousOn_const
  have gLeft : EqOn g (fun _ => (0 : ℂ)) left :=
    Measure.eqOn_open_of_ae_eq hleft left_open (hg.continuousOn.mono inter_subset_left) continuousOn_const
  have hc : ContinuousAt g 0 := hg.continuousOn.continuousAt
    (disk_open.mem_nhds (by simp [disk]))
  have h1 : g 0 = 1 := hc.continuousWithinAt.eq_const_of_mem_closure zero_mem_closure_right gRight
  have h0 : g 0 = 0 := hc.continuousWithinAt.eq_const_of_mem_closure zero_mem_closure_left gLeft
  exact one_ne_zero (h1.symm.trans h0)

example : vector ∉ Bergman ∧ vector ≠ 0 := by
  refine ⟨vector_not_mem, ?_⟩
  intro h
  exact vector_not_mem (h.symm ▸ Bergman.zero_mem)

example :
    (AnalyticL2.projection disk disk_open vector : Lp ℂ 2 (volume.restrict disk)) ≠ vector := by
  intro h
  exact vector_not_mem (h ▸ (AnalyticL2.projection disk disk_open vector).property)

example :
    0 < ‖vector - (AnalyticL2.projection disk disk_open vector : Lp ℂ 2 (volume.restrict disk))‖ := by
  apply norm_pos_iff.mpr
  intro h
  have heq := sub_eq_zero.mp h
  exact vector_not_mem (heq.symm ▸ (AnalyticL2.projection disk disk_open vector).property)

example :
    AnalyticL2.projection disk disk_open
      (AnalyticL2.projection disk disk_open vector : Lp ℂ 2 (volume.restrict disk)) =
        AnalyticL2.projection disk disk_open vector := by
  change Bergman.orthogonalProjectionOnto
    (Bergman.orthogonalProjectionOnto vector : Lp ℂ 2 (volume.restrict disk)) = _
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _

end MathlibExtTest.ProjectionNonmember
