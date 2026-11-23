/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Diffusion.SelectionTimes

/-! Tests for the mean absorption time under genic selection: the boundary-value problem
restated, the boundary values and the relabeling symmetry at concrete parameter values, the
neutral value `T_0(1/2) = 2 log 2`, and the weak-selection limit restated. -/

open Real Set Filter
open scoped Topology

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.SelectionTimes

open MathlibExt.Biology.PopulationGenetics.Diffusion

/-- `T_σ` is the Green integral of the sojourn kernel. -/
example (σ p : ℝ) : selectionMeanAbsorptionTime σ p = ∫ x in (0 : ℝ)..1, selectionGreen σ p x :=
  rfl

/-- The backward equation `L_σ T_σ = -1`, restated. -/
example (σ : ℝ) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    generator σ (selectionMeanAbsorptionTime σ) p = -1 :=
  generator_selectionMeanAbsorptionTime σ hp

/-- The boundary values, restated. -/
example (σ : ℝ) : selectionMeanAbsorptionTime σ 0 = 0 := selectionMeanAbsorptionTime_left σ
example (σ : ℝ) : selectionMeanAbsorptionTime σ 1 = 0 := selectionMeanAbsorptionTime_right σ

/-- Continuity on the closed interval, restated. -/
example (σ : ℝ) : ContinuousOn (selectionMeanAbsorptionTime σ) (Icc 0 1) :=
  continuousOn_selectionMeanAbsorptionTime σ

/-- The kernel relabeling symmetry, restated. -/
example (σ p x : ℝ) : selectionGreen (-σ) (1 - p) (1 - x) = selectionGreen σ p x :=
  selectionGreen_neg_one_sub σ p x

/-- The relabeling symmetry of `T`, at concrete values: `T_{-2}(3/4) = T_2(1/4)`. -/
example : selectionMeanAbsorptionTime (-2) (1 - 1 / 4) = selectionMeanAbsorptionTime 2 (1 / 4) :=
  selectionMeanAbsorptionTime_neg_one_sub 2 (1 / 4)

/-- At neutrality `T_0` is the Kimura–Ohta time, restated. -/
example {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    selectionMeanAbsorptionTime 0 p = meanAbsorptionTime p :=
  selectionMeanAbsorptionTime_zero hp

/-- The neutral value at `p = 1/2`: `T_0(1/2) = 2 log 2`. -/
example : selectionMeanAbsorptionTime 0 (1 / 2) = 2 * log 2 := by
  rw [selectionMeanAbsorptionTime_zero ⟨by norm_num, by norm_num⟩, meanAbsorptionTime]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, one_div, Real.log_inv]
  ring

/-- The weak-selection limit, restated: `T_σ(p) → T(p)` as `σ → 0`. -/
example {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun σ => selectionMeanAbsorptionTime σ p) (𝓝 0) (𝓝 (meanAbsorptionTime p)) :=
  tendsto_selectionMeanAbsorptionTime_zero hp

/-- The limit at the concrete frequency `p = 1/2` is `2 log 2`. -/
example : Tendsto (fun σ => selectionMeanAbsorptionTime σ (1 / 2)) (𝓝 0) (𝓝 (2 * log 2)) := by
  have h := tendsto_selectionMeanAbsorptionTime_zero (p := 1 / 2) ⟨by norm_num, by norm_num⟩
  rw [show meanAbsorptionTime (1 / 2 : ℝ) = 2 * log 2 by
    rw [meanAbsorptionTime, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, one_div, Real.log_inv]
    ring] at h
  exact h

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.SelectionTimes
