/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Babak Modami
-/
module

public import MathlibExt.Topology.MetricSpace.Lipschitz.L1Distortion

@[expose] public section

open MeasureTheory

namespace MathlibExtTest.Topology.MetricSpace.Lipschitz.L1Distortion

open MetaMathlibExt

-- Geometry 514: L1 distortion of a metric space

/-The lemma extracts the first conjunct of IsStdL1EmbeddingWithDistortion:
 any D that is claimed to be an admissible L₁ distortion must satisfy D≥ 1 -/

lemma hasDistortion_ge_one {X ρ D}
    (h : HasStdL1DistortionLe X ρ D) : 1 ≤ D := by
  obtain ⟨_, h1, _⟩ := h
  exact h1

/-The lemma shows that c₁(X,ρ) ≥ 1-/

lemma c1_ge_one (X : Type*) (ρ : X × X → ℝ) : 1 ≤ c1 X ρ := by
  classical
  unfold c1
  by_cases h : ({D | HasStdL1DistortionLe X ρ D}).Nonempty
  · have h_neT : ((WithTop.some : ℝ → WithTop ℝ) '' {D | HasStdL1DistortionLe X ρ D}).Nonempty := by
      obtain ⟨D, hD⟩ := h
      exact ⟨↑D, D, hD, rfl⟩
    apply le_csInf h_neT
    rintro y ⟨D, hD, rfl⟩
    exact WithTop.coe_le_coe.mpr (hasDistortion_ge_one hD)
  · have h_empty : {D | HasStdL1DistortionLe X ρ D} = ∅ := by
      ext x
      simp
      intro hx
      exact h ⟨x, hx⟩
    rw [h_empty]
    simp

end MathlibExtTest.Topology.MetricSpace.Lipschitz.L1Distortion

end
