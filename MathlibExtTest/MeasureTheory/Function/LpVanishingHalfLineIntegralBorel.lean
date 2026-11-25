/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.LpVanishingHalfLineIntegralBorel
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum

open Filter MeasureTheory Set
open MathlibExt.MeasureTheory.LpVanishingHalfLineIntegralBorelWanted
open scoped ENNReal Topology

private noncomputable def step (p : ℝ≥0∞) (a b : ℝ) : Lp ℝ p (volume : Measure ℝ) :=
  indicatorConstLp p measurableSet_Icc (isCompact_Icc (a := a) (b := b)).measure_lt_top.ne 1

-- A nonzero step function supported on the negative half-line is in the set.
example : step 1 (-2) (-1) ∈ vanishingIntegralSet 1 := by
  change Tendsto (fun L : ℝ => ∫ x in Icc 0 L, step 1 (-2) (-1) x ∂volume) atTop (𝓝 0)
  refine tendsto_const_nhds.congr fun L => ?_
  have hdisj : Icc (-2 : ℝ) (-1) ∩ Icc 0 L = ∅ :=
    disjoint_iff_inter_eq_empty.mp (disjoint_left.mpr fun x hx hy => by
      have h : (0 : ℝ) ≤ -1 := hy.1.trans hx.2
      norm_num at h)
  rw [step, setIntegral_indicatorConstLp measurableSet_Icc measurableSet_Icc,
    hdisj, measureReal_empty, zero_smul]

-- At p = ∞, this step function has limiting integral one, not zero.
example : step ∞ 0 1 ∉ vanishingIntegralSet ∞ := by
  intro h
  change Tendsto (fun L : ℝ => ∫ x in Icc 0 L, step ∞ 0 1 x ∂volume) atTop (𝓝 0) at h
  have he : (fun L : ℝ => ∫ x in Icc 0 L, step ∞ 0 1 x ∂volume) =ᶠ[atTop] fun _ => (1 : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hs : Icc (0 : ℝ) 1 ⊆ Icc 0 L := Icc_subset_Icc_right hL
    rw [step, setIntegral_indicatorConstLp measurableSet_Icc measurableSet_Icc,
      inter_eq_left.mpr hs, Real.volume_real_Icc_of_le (by norm_num), sub_zero, one_smul]
  exact zero_ne_one (tendsto_nhds_unique h (tendsto_const_nhds.congr' he.symm))

example : @MeasurableSet (Lp ℝ ∞ (volume : Measure ℝ)) (borel _) (vanishingIntegralSet ∞) := by
  let : Fact ((1 : ℝ≥0∞) ≤ ∞) := ⟨le_top⟩
  exact measurableSet_vanishingIntegralSet ∞
