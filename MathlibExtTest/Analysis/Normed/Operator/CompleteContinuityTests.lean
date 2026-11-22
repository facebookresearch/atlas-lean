/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Operator.CompleteContinuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Tests for complete continuity of compact operators

The identity operator on a finite-dimensional space is compact, so the
complete-continuity theorems apply to it; the zero operator is compact
on any space. The sequences `1 / (n + 1)` converge weakly (in fact in
norm) to `0` in `ℝ` and in `ℂ`.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.Normed.Operator.CompleteContinuityTests

open Filter Topology
open scoped Complex
open MathlibExt.Analysis.Normed.Operator.CompleteContinuity

/-- The identity on `ℝ` is compact (finite-dimensionality). -/
private theorem isCompactOperator_id_real :
    IsCompactOperator ((ContinuousLinearMap.id ℝ ℝ : ℝ →L[ℝ] ℝ) : ℝ → ℝ) := by
  simpa using isCompactOperator_id (E := ℝ)

/-- The identity on `ℂ` is compact (finite-dimensionality). -/
private theorem isCompactOperator_id_complex :
    IsCompactOperator ((ContinuousLinearMap.id ℂ ℂ : ℂ →L[ℂ] ℂ) : ℂ → ℂ) := by
  simpa using isCompactOperator_id (E := ℂ)

example : Tendsto (fun n : ℕ => (ContinuousLinearMap.id ℝ ℝ) (1 / ((n : ℝ) + 1)))
    atTop (𝓝 ((ContinuousLinearMap.id ℝ ℝ) 0)) := by
  apply tendsto_apply_of_isCompactOperator_of_forall_tendsto isCompactOperator_id_real
  intro f
  have hu : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact (f.continuous.tendsto 0).comp hu

example : Tendsto (fun n : ℕ => (ContinuousLinearMap.id ℂ ℂ) (1 / ((n : ℂ) + 1)))
    atTop (𝓝 0) := by
  apply tendsto_apply_of_isCompactOperator_of_tendsto_zero isCompactOperator_id_complex
  intro f
  have hu : Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h := (f.continuous.tendsto 0).comp hu
  rw [map_zero f] at h
  exact h

example : Tendsto (fun n : ℕ =>
    (ContinuousLinearMap.id ℝ ℝ) (1 / ((n : ℝ) + 1)))
    atTop (𝓝 ((ContinuousLinearMap.id ℝ ℝ) 0)) := by
  apply tendsto_apply_of_isCompactOperator_of_tendsto_weakSpace isCompactOperator_id_real
  have hu : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hweak : Tendsto (fun n : ℕ => toWeakSpace ℝ ℝ (1 / ((n : ℝ) + 1)))
      atTop (𝓝 (toWeakSpace ℝ ℝ (0 : ℝ))) :=
    (toWeakSpaceCLM ℝ ℝ).continuous.tendsto 0 |>.comp hu
  simpa using hweak

example : Tendsto (fun n : ℕ => (0 : ℝ →L[ℝ] ℝ) (1 / ((n : ℝ) + 1)))
    atTop (𝓝 ((0 : ℝ →L[ℝ] ℝ) 0)) := by
  apply tendsto_apply_of_isCompactOperator_of_forall_tendsto
  · simpa using isCompactOperator_zero (M₁ := ℝ) (M₂ := ℝ)
  · intro f
    have hu : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact (f.continuous.tendsto 0).comp hu

end MathlibExtTest.Analysis.Normed.Operator.CompleteContinuityTests
