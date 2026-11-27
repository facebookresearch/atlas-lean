/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Control.Barbalat

/-! # Half-line hypothesis of Barbălat's lemma -/

open Filter Set
open scoped Topology

-- The function jumps at zero, but its restriction to the nonnegative half-line is constant.
example : Tendsto (fun x : ℝ => if x < 0 then (1 : ℝ) else 0) atTop (𝓝 0) := by
  let f (x : ℝ) : ℝ := if x < 0 then 1 else 0
  have hf₀ (x : ℝ) (hx : 0 ≤ x) : f x = 0 := by simp [f, not_lt_of_ge hx]
  have hf : UniformContinuousOn f (Ici 0) := by
    rw [Metric.uniformContinuousOn_iff]
    intro ε hε
    refine ⟨1, zero_lt_one, fun x hx y hy _ => ?_⟩
    simpa [hf₀ x hx, hf₀ y hy] using hε
  have hlim : Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..t, f s) atTop (𝓝 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    symm
    calc
      (∫ s in (0 : ℝ)..t, f s) = ∫ _ in (0 : ℝ)..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ht] at hs
        exact hf₀ s hs.1
      _ = 0 := by simp
  exact MetaMathlibExt.tendsto_zero_of_uniformContinuousOn_Ici_of_integral_tendsto hf hlim
