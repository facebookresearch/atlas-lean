/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Fourier.HalfSpaceLaplaceDecayEstimate

open MathlibExt.Analysis.Fourier.HalfSpaceLaplaceDecayEstimateWanted

-- The two horizontal coordinates survive the embedding in their original order.
example (x : R2) (z : ℝ) : point3 x z 0 = x 0 ∧ point3 x z 1 = x 1 := by
  simp [point3]

-- The boundary plane belongs to the closed domain and is excluded from the harmonicity domain.
example (x : R2) : point3 x 0 ∈ LowerHalfSpace ∧ point3 x 0 ∉ OpenLowerHalfSpace := by
  simp [LowerHalfSpace, OpenLowerHalfSpace, point3]

example (x : R2) (z : ℝ) : point3 x z ∈ OpenLowerHalfSpace ↔ z < 0 := by
  simp [OpenLowerHalfSpace, point3]

-- The zero trace and its extension satisfy all hypotheses, including uniform decay.
example : ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, z ≤ 0 → ∀ _x : R2, |(0 : ℝ)| ≤ C * (1 + |z|)⁻¹ := by
  apply exists_abs_le_inv_one_add_abs_of_harmonic_lowerHalfSpace
    (φ := 0) (u := fun _ => 0) (InnerProductSpace.harmonicOnNhd_const 0) continuousOn_const
  · exact ⟨0, by simp⟩
  · simp
  · intro ε hε
    exact Filter.Eventually.of_forall fun _ _ => by simpa using hε
