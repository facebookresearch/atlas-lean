/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Measure.ParamSmooth

open MeasureTheory

/-- A zero-function smoke test of smoothness of parameter integrals. -/
example : ContDiff ℝ (⊤ : ℕ∞)
    (fun _p : ℝ => ∫ _x : ℝ, (0 : ℝ) • (0 : ℝ) ∂(volume : Measure ℝ)) := by
  have h := MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
    (X := ℝ) (μ := volume) (M := ℝ) (P := ℝ) (E := ℝ)
    (fun _ => (0 : ℝ)) continuous_const (fun _ => (0 : ℝ)) continuous_const
    (by simp [HasCompactSupport]) (fun _ => (0 : ℝ)) contDiff_const
    (by simp [HasCompactSupport])
  exact h
