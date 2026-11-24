/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import MathlibExt.Analysis.Distribution.CauchyPrincipalValue

open Filter MeasureTheory Set
open scoped SchwartzMap

namespace MathlibExt.Analysis.Distribution.CauchyPrincipalValueWanted

-- A bump equal to one near zero has a singular quotient and principal value zero.
example : ∃ φ : 𝓢(ℝ, ℝ), φ 0 = 1 ∧ ∃ L : ℝ,
    Tendsto (fun ε : ℝ => ∫ x in {x : ℝ | ε ≤ |x|}, φ x / x ∂volume)
      (nhdsWithin 0 (Ioi 0)) (nhds L) ∧ L = 0 := by
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let φ := bump.hasCompactSupport.toSchwartzMap bump.contDiff
  have hφ : φ 0 = 1 :=
    bump.one_of_mem_closedBall (Metric.mem_closedBall_self bump.rIn_pos.le)
  obtain ⟨L, hL⟩ := cauchyPrincipalValue_exists φ
  refine ⟨φ, hφ, L, hL, ?_⟩
  have hzero (ε : ℝ) : (∫ x in {x : ℝ | ε ≤ |x|}, φ x / x) = 0 := by
    let s : Set ℝ := {x : ℝ | ε ≤ |x|}
    have hs : MeasurableSet s := measurableSet_le measurable_const continuous_abs.measurable
    rw [← integral_indicator hs]
    let f : ℝ → ℝ := s.indicator (fun x => φ x / x)
    change (∫ x, f x) = 0
    have hodd (x : ℝ) : f (-x) = -f x := by
      have heven : φ (-x) = φ x := bump.neg x
      by_cases hx : ε ≤ |x| <;> simp [f, s, hx, heven, div_neg]
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding f
    change (∫ x, f (-x)) = ∫ x, f x at h
    simp_rw [hodd, integral_neg] at h
    linarith
  apply tendsto_nhds_unique hL
  simpa only [hzero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (nhdsWithin 0 (Ioi 0)) (nhds 0))

end MathlibExt.Analysis.Distribution.CauchyPrincipalValueWanted
