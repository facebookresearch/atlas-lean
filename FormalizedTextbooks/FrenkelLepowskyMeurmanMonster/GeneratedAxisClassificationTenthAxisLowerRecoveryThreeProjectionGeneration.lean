/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0000
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0002
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0100
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0101
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0102
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0200
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0201
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0202
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0300
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0301
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0302
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0400
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0401
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0402
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0500
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0501
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0502
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0600
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0601
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0602
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0700
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0701
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0702
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0800
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0801
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0802
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0900
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0901
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates0902
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates1000
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates1001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionCoordinates1002

/-! All264 full original column certificates join symbolically. Three genuine
full-axis projected lifts suffice only after all eleven actual spatial binary
bindings have been proved; no source identity is inferred from discovery. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete original signed word of every candidate matches every24-bit column. -/
theorem generatedTenth_axis_lower_recovery_three_projection_complete_words
    (i : Fin 11) (j : Fin 24) :
    generatedTenthAxisLowerRecoveryThreeProjectionMaskWord
      (generatedTenthAxisLowerRecoveryThreeProjectionWords i) (2 ^ j.val) =
      generatedTenthAxisLowerRecoveryCompactBinaryColumns i j := by
  let u : Fin 8 := ⟨j.val % 8, Nat.mod_lt _ (by decide)⟩
  have hj : j.val = 8 * (j.val / 8) + u.val := by dsimp [u]; omega
  have hq : j.val / 8 = 0 ∨ j.val / 8 = 1 ∨ j.val / 8 = 2 := by omega
  fin_cases i
  · change generatedTenthAxisLowerRecoveryThreeProjectionMaskWord
      (generatedTenthAxisLowerRecoveryThreeProjectionWords 0) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns 0 j
    rcases hq with hq | hq | hq
    · have hv : 8 * 0 + u.val = j.val := by omega
      have he : (⟨8 * 0 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_00_00 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 1 + u.val = j.val := by omega
      have he : (⟨8 * 1 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_00_01 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 2 + u.val = j.val := by omega
      have he : (⟨8 * 2 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_00_02 u
      rw [he, hv] at hc
      exact hc
  · change generatedTenthAxisLowerRecoveryThreeProjectionMaskWord
      (generatedTenthAxisLowerRecoveryThreeProjectionWords 1) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns 1 j
    rcases hq with hq | hq | hq
    · have hv : 8 * 0 + u.val = j.val := by omega
      have he : (⟨8 * 0 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_01_00 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 1 + u.val = j.val := by omega
      have he : (⟨8 * 1 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_01_01 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 2 + u.val = j.val := by omega
      have he : (⟨8 * 2 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_01_02 u
      rw [he, hv] at hc
      exact hc
  · change generatedTenthAxisLowerRecoveryThreeProjectionMaskWord
      (generatedTenthAxisLowerRecoveryThreeProjectionWords 2) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns 2 j
    rcases hq with hq | hq | hq
    · have hv : 8 * 0 + u.val = j.val := by omega
      have he : (⟨8 * 0 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_02_00 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 1 + u.val = j.val := by omega
      have he : (⟨8 * 1 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_02_01 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 2 + u.val = j.val := by omega
      have he : (⟨8 * 2 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_02_02 u
      rw [he, hv] at hc
      exact hc
  · change generatedTenthAxisLowerRecoveryThreeProjectionMaskWord
      (generatedTenthAxisLowerRecoveryThreeProjectionWords 3) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns 3 j
    rcases hq with hq | hq | hq
    · have hv : 8 * 0 + u.val = j.val := by omega
      have he : (⟨8 * 0 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_03_00 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 1 + u.val = j.val := by omega
      have he : (⟨8 * 1 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_03_01 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 2 + u.val = j.val := by omega
      have he : (⟨8 * 2 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_03_02 u
      rw [he, hv] at hc
      exact hc
  · change generatedTenthAxisLowerRecoveryThreeProjectionMaskWord
      (generatedTenthAxisLowerRecoveryThreeProjectionWords 4) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns 4 j
    rcases hq with hq | hq | hq
    · have hv : 8 * 0 + u.val = j.val := by omega
      have he : (⟨8 * 0 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_04_00 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 1 + u.val = j.val := by omega
      have he : (⟨8 * 1 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_04_01 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 2 + u.val = j.val := by omega
      have he : (⟨8 * 2 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_04_02 u
      rw [he, hv] at hc
      exact hc
  · change generatedTenthAxisLowerRecoveryThreeProjectionMaskWord
      (generatedTenthAxisLowerRecoveryThreeProjectionWords 5) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns 5 j
    rcases hq with hq | hq | hq
    · have hv : 8 * 0 + u.val = j.val := by omega
      have he : (⟨8 * 0 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_05_00 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 1 + u.val = j.val := by omega
      have he : (⟨8 * 1 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_05_01 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 2 + u.val = j.val := by omega
      have he : (⟨8 * 2 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_05_02 u
      rw [he, hv] at hc
      exact hc
  · change generatedTenthAxisLowerRecoveryThreeProjectionMaskWord
      (generatedTenthAxisLowerRecoveryThreeProjectionWords 6) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns 6 j
    rcases hq with hq | hq | hq
    · have hv : 8 * 0 + u.val = j.val := by omega
      have he : (⟨8 * 0 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_06_00 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 1 + u.val = j.val := by omega
      have he : (⟨8 * 1 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_06_01 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 2 + u.val = j.val := by omega
      have he : (⟨8 * 2 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_06_02 u
      rw [he, hv] at hc
      exact hc
  · change generatedTenthAxisLowerRecoveryThreeProjectionMaskWord
      (generatedTenthAxisLowerRecoveryThreeProjectionWords 7) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns 7 j
    rcases hq with hq | hq | hq
    · have hv : 8 * 0 + u.val = j.val := by omega
      have he : (⟨8 * 0 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_07_00 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 1 + u.val = j.val := by omega
      have he : (⟨8 * 1 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_07_01 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 2 + u.val = j.val := by omega
      have he : (⟨8 * 2 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_07_02 u
      rw [he, hv] at hc
      exact hc
  · change generatedTenthAxisLowerRecoveryThreeProjectionMaskWord
      (generatedTenthAxisLowerRecoveryThreeProjectionWords 8) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns 8 j
    rcases hq with hq | hq | hq
    · have hv : 8 * 0 + u.val = j.val := by omega
      have he : (⟨8 * 0 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_08_00 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 1 + u.val = j.val := by omega
      have he : (⟨8 * 1 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_08_01 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 2 + u.val = j.val := by omega
      have he : (⟨8 * 2 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_08_02 u
      rw [he, hv] at hc
      exact hc
  · change generatedTenthAxisLowerRecoveryThreeProjectionMaskWord
      (generatedTenthAxisLowerRecoveryThreeProjectionWords 9) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns 9 j
    rcases hq with hq | hq | hq
    · have hv : 8 * 0 + u.val = j.val := by omega
      have he : (⟨8 * 0 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_09_00 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 1 + u.val = j.val := by omega
      have he : (⟨8 * 1 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_09_01 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 2 + u.val = j.val := by omega
      have he : (⟨8 * 2 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_09_02 u
      rw [he, hv] at hc
      exact hc
  · change generatedTenthAxisLowerRecoveryThreeProjectionMaskWord
      (generatedTenthAxisLowerRecoveryThreeProjectionWords 10) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns 10 j
    rcases hq with hq | hq | hq
    · have hv : 8 * 0 + u.val = j.val := by omega
      have he : (⟨8 * 0 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_10_00 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 1 + u.val = j.val := by omega
      have he : (⟨8 * 1 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_10_01 u
      rw [he, hv] at hc
      exact hc
    · have hv : 8 * 2 + u.val = j.val := by omega
      have he : (⟨8 * 2 + u.val, by omega⟩ : Fin 24) = j := Fin.ext hv
      have hc := generatedTenth_axis_lower_recovery_three_projection_coordinates_10_02 u
      rw [he, hv] at hc
      exact hc

/-- Full actual source binding identifies all eleven genuine projected source words. -/
theorem generatedTenth_axis_lower_recovery_three_projection_candidate_word
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (i : Fin 11) :
    generatedTenthAxisLowerRecoveryThreeProjectionActual i =
      generatedTenthAxisLowerRecoveryThreeProjectionWord
      (generatedTenthAxisLowerRecoveryThreeProjectionWords i) :=
  generatedTenth_axis_lower_recovery_three_projection_candidate_word_of_certificate hsource
    generatedTenth_axis_lower_recovery_three_projection_complete_words i

/-- Three genuine full-axis projected source values attain all eleven. -/
theorem generatedTenth_axis_lower_recovery_three_projection_candidates_mem
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (P : Subgroup Co1)
    (h : ∀ g : Fin 3, generatedTenthAxisLowerRecoveryThreeProjectionActual
      (generatedTenthAxisLowerRecoveryThreeProjectionCandidateIndex g) ∈ P) (i : Fin 11) :
    generatedTenthAxisLowerRecoveryThreeProjectionActual i ∈ P :=
  generatedTenth_axis_lower_recovery_three_projection_mem_of_certificate hsource
    generatedTenth_axis_lower_recovery_three_projection_complete_words P h i

/-- Only original candidates9,10,1 need full-axis lifts, with all source bindings explicit. -/
theorem generatedTenth_axis_lower_recovery_three_projection_local_card
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (hlifts : ∀ g : Fin 3,
      generatedTenthAxisLowerRecoveryThreeProjectionActual
        (generatedTenthAxisLowerRecoveryThreeProjectionCandidateIndex g) ∈
        generatedTenthProjectedAxisStabilizer) :
    Nat.card generatedTenthLocalAxisStabilizer = 2903040 := by
  have hall := generatedTenth_axis_lower_recovery_three_projection_candidates_mem hsource
    generatedTenthProjectedAxisStabilizer hlifts
  apply generatedTenth_axis_lower_recovery_eleven_projection_values
  · intro k
    have h := hall ⟨k.val, by omega⟩
    have hk : k.val < 7 := k.isLt
    simpa only [generatedTenthAxisLowerRecoveryThreeProjectionActual,
      generatedTenthAxisLowerRecoveryCompactSpatial,
      generatedTenthAxisLowerRecoveryCompactStandardSpatial, hk, ↓reduceDIte,
      generatedTenthAxisLowerRecoveryOriginalProjection, MonoidHom.comp_apply] using h
  · intro k
    have h := hall ⟨k.val + 7, by omega⟩
    have hk7 : ¬k.val + 7 < 7 := by omega
    have hk9 : k.val + 7 < 9 := by omega
    have hk : k.val + 7 - 7 = k.val := by omega
    simpa only [generatedTenthAxisLowerRecoveryThreeProjectionActual,
      generatedTenthAxisLowerRecoveryCompactSpatial,
      generatedTenthAxisLowerRecoveryCompactStandardSpatial, hk7, hk9, ↓reduceDIte, hk,
      generatedTenthAxisLowerRecoveryOriginalProjection, MonoidHom.comp_apply] using h
  · intro k
    have h := hall ⟨k.val + 9, by omega⟩
    have hk7 : ¬k.val + 9 < 7 := by omega
    have hk9 : ¬k.val + 9 < 9 := by omega
    have hk : k.val + 9 - 9 = k.val := by omega
    simpa only [generatedTenthAxisLowerRecoveryThreeProjectionActual,
      generatedTenthAxisLowerRecoveryCompactSpatial,
      generatedTenthAxisLowerRecoveryCompactStandardSpatial, hk7, hk9, ↓reduceDIte, hk,
      generatedTenthAxisLowerRecoveryOriginalProjection, MonoidHom.comp_apply] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
