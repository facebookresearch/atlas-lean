/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoProjectionCoordinates0000
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoProjectionCoordinates0001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoProjectionCoordinates0002
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoProjectionCoordinates0100
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoProjectionCoordinates0101
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoProjectionCoordinates0102
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoProjectionCoordinates0200
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoProjectionCoordinates0201
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoProjectionCoordinates0202
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionGeneration

/-! Nine bounded leaves cover all72 original word columns. Two genuine full-axis
projected memberships imply the existing three-generator lower assembly, while
all original spatial binary source bindings remain explicit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

theorem generatedTenth_axis_lower_recovery_two_projection_complete_words
    (i : Fin 3) (j : Fin 24) :
    generatedTenthAxisLowerRecoveryTwoProjectionMaskWord
      (generatedTenthAxisLowerRecoveryTwoProjectionWords i) (2 ^ j.val) =
      generatedTenthAxisLowerRecoveryCompactBinaryColumns
        (generatedTenthAxisLowerRecoveryTwoProjectionCandidateIndex i) j := by
  let u : Fin 8 := ⟨j.val % 8, Nat.mod_lt _ (by decide)⟩
  have hj : j.val = 8 * (j.val / 8) + u.val := by dsimp [u]; omega
  have hq : j.val / 8 = 0 ∨ j.val / 8 = 1 ∨ j.val / 8 = 2 := by omega
  fin_cases i
  · change generatedTenthAxisLowerRecoveryTwoProjectionMaskWord
      (generatedTenthAxisLowerRecoveryTwoProjectionWords 0) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns
          (generatedTenthAxisLowerRecoveryTwoProjectionCandidateIndex 0) j
    rcases hq with hq | hq | hq
    · have hv : 8 * 0 + u.val = j.val := by omega
      have he : (⟨8 * 0 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_two_projection_coordinates_00_00 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 1 + u.val = j.val := by omega
      have he : (⟨8 * 1 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_two_projection_coordinates_00_01 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 2 + u.val = j.val := by omega
      have he : (⟨8 * 2 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_two_projection_coordinates_00_02 u
      rw [he, hv] at hc
      exact hc
  · change generatedTenthAxisLowerRecoveryTwoProjectionMaskWord
      (generatedTenthAxisLowerRecoveryTwoProjectionWords 1) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns
          (generatedTenthAxisLowerRecoveryTwoProjectionCandidateIndex 1) j
    rcases hq with hq | hq | hq
    · have hv : 8 * 0 + u.val = j.val := by omega
      have he : (⟨8 * 0 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_two_projection_coordinates_01_00 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 1 + u.val = j.val := by omega
      have he : (⟨8 * 1 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_two_projection_coordinates_01_01 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 2 + u.val = j.val := by omega
      have he : (⟨8 * 2 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_two_projection_coordinates_01_02 u
      rw [he, hv] at hc
      exact hc
  · change generatedTenthAxisLowerRecoveryTwoProjectionMaskWord
      (generatedTenthAxisLowerRecoveryTwoProjectionWords 2) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns
          (generatedTenthAxisLowerRecoveryTwoProjectionCandidateIndex 2) j
    rcases hq with hq | hq | hq
    · have hv : 8 * 0 + u.val = j.val := by omega
      have he : (⟨8 * 0 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_two_projection_coordinates_02_00 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 1 + u.val = j.val := by omega
      have he : (⟨8 * 1 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_two_projection_coordinates_02_01 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 2 + u.val = j.val := by omega
      have he : (⟨8 * 2 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_two_projection_coordinates_02_02 u
      rw [he, hv] at hc
      exact hc

/-- The two actual projected source memberships supply all three original memberships. -/
theorem generatedTenth_axis_lower_recovery_two_projection_three_mem
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (P : Subgroup Co1) (h : ∀ g : Fin 2, generatedTenthAxisLowerRecoveryTwoProjectionActual g ∈ P)
      (g : Fin 3) :
    generatedTenthAxisLowerRecoveryThreeProjectionActual
      (generatedTenthAxisLowerRecoveryThreeProjectionCandidateIndex g) ∈ P := by
  have hs := generatedTenth_axis_lower_recovery_two_projection_mem_of_certificate hsource
    generatedTenth_axis_lower_recovery_two_projection_complete_words P h
  fin_cases g
  · change generatedTenthAxisLowerRecoveryThreeProjectionActual 9 ∈ P
    have hg := hs 1
    change generatedTenthAxisLowerRecoveryThreeProjectionActual 9 ∈ P at hg
    exact hg
  · change generatedTenthAxisLowerRecoveryThreeProjectionActual 10 ∈ P
    have hg := hs 2
    change generatedTenthAxisLowerRecoveryThreeProjectionActual 10 ∈ P at hg
    exact hg
  · change generatedTenthAxisLowerRecoveryThreeProjectionActual 1 ∈ P
    have hg := hs 0
    change generatedTenthAxisLowerRecoveryThreeProjectionActual 1 ∈ P at hg
    exact hg

/-- The literal joint9*1 and original10 full-axis projections close the full actual matrix image. -/
theorem generatedTenth_axis_lower_recovery_two_projection_candidates_mem
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (P : Subgroup Co1) (h : ∀ g : Fin 2, generatedTenthAxisLowerRecoveryTwoProjectionActual g ∈ P)
      (i : Fin 11) :
    generatedTenthAxisLowerRecoveryThreeProjectionActual i ∈ P :=
  generatedTenth_axis_lower_recovery_three_projection_candidates_mem hsource P
    (generatedTenth_axis_lower_recovery_two_projection_three_mem hsource P h) i

/-- Exact full-axis lower assembly has only two genuine fixation obligations left. -/
theorem generatedTenth_axis_lower_recovery_two_projection_local_card
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (hlifts : ∀ g : Fin 2, generatedTenthAxisLowerRecoveryTwoProjectionActual g ∈
      generatedTenthProjectedAxisStabilizer) :
    Nat.card generatedTenthLocalAxisStabilizer = 2903040 := by
  exact generatedTenth_axis_lower_recovery_three_projection_local_card hsource
    (generatedTenth_axis_lower_recovery_two_projection_three_mem hsource
      generatedTenthProjectedAxisStabilizer hlifts)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
