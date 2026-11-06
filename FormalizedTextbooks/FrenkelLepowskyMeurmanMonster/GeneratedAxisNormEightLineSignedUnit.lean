/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineStabilizer

/-! The actual coordinate-line stabilizer preserves its real unit vector up to a genuine sign. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

theorem generatedNormEightVector_axis_unit :
    generatedNormEightVector leechNormEightAxis =
      (8 / Real.sqrt 8 : ℝ) • (Pi.single 0 1 : Fin 24 → ℝ) := by
  ext i
  change (leechCoordinateFrameVector 0 i : ℝ) / Real.sqrt 8 = _
  by_cases h : i = 0 <;> simp [leechCoordinateFrameVector, h]

/-- The genuine physical line stabilizer takes its coordinate unit vector
to one of its two signs. -/
theorem generatedNormEightLineStabilizer_signed_unit (g : leechIsomSubgroup)
    (hg : g ∈ generatedNormEightLineStabilizer) :
    ∃ b : ZMod 2, g.val (Pi.single 0 1) = qSign b • (Pi.single 0 1 : Fin 24 → ℝ) := by
  have hm := (generatedNormEightLineStabilizer_mem g).mp hg
  rw [← generatedNormEightLineMatrix_action] at hm
  have he : generatedNormEightVector (g • leechNormEightAxis) =
      g.val (generatedNormEightVector leechNormEightAxis) :=
    leechIntegralAction_embedding g leechNormEightAxis.val
  have hc : (8 / Real.sqrt 8 : ℝ) ≠ 0 :=
    div_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  rcases (generatedNormEightLineMatrix_eq_iff leechNormEightAxis (g • leechNormEightAxis)).mp
      hm.symm with hp | hn
  · rw [hp, generatedNormEightVector_axis_unit, map_smul] at he
    refine ⟨0, ?_⟩
    rw [qSign_zero, one_smul]
    exact (smul_right_injective (Fin 24 → ℝ) hc he).symm
  · rw [hn, generatedNormEightVector_neg, generatedNormEightVector_axis_unit, map_smul] at he
    refine ⟨1, ?_⟩
    rw [qSign_one, neg_one_smul]
    apply smul_right_injective (Fin 24 → ℝ) hc
    change (8 / Real.sqrt 8 : ℝ) • g.val (Pi.single 0 1) =
      (8 / Real.sqrt 8 : ℝ) • -(Pi.single 0 1 : Fin 24 → ℝ)
    rw [smul_neg]
    exact he.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
