/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastFormula
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck18
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastCheck23

/-! All original octad catalogue checks discharge the complete bounded preferred-mask formula. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Every bounded original catalogue code and physical coordinate is fully verified. -/
theorem generatedAxisGlobalPreferredMaskOctad_actual (j : Fin 759) :
    generatedAxisGlobalPreferredMaskOctadCode j = generatedAxisGlobalOctadCodeData j ∧
    ∀ k : Fin 8, generatedAxisGlobalPreferredMaskOctadCoordinate j k =
      generatedAxisGlobalOctadCoordinatesData j k := by
  by_cases h00 : j.val < 32
  · let i : Fin 32 := ⟨j.val-0, by omega⟩
    have hj : (⟨0+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck00 i
    rw [hj] at h
    exact h
  by_cases h01 : j.val < 64
  · let i : Fin 32 := ⟨j.val-32, by omega⟩
    have hj : (⟨32+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck01 i
    rw [hj] at h
    exact h
  by_cases h02 : j.val < 96
  · let i : Fin 32 := ⟨j.val-64, by omega⟩
    have hj : (⟨64+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck02 i
    rw [hj] at h
    exact h
  by_cases h03 : j.val < 128
  · let i : Fin 32 := ⟨j.val-96, by omega⟩
    have hj : (⟨96+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck03 i
    rw [hj] at h
    exact h
  by_cases h04 : j.val < 160
  · let i : Fin 32 := ⟨j.val-128, by omega⟩
    have hj : (⟨128+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck04 i
    rw [hj] at h
    exact h
  by_cases h05 : j.val < 192
  · let i : Fin 32 := ⟨j.val-160, by omega⟩
    have hj : (⟨160+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck05 i
    rw [hj] at h
    exact h
  by_cases h06 : j.val < 224
  · let i : Fin 32 := ⟨j.val-192, by omega⟩
    have hj : (⟨192+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck06 i
    rw [hj] at h
    exact h
  by_cases h07 : j.val < 256
  · let i : Fin 32 := ⟨j.val-224, by omega⟩
    have hj : (⟨224+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck07 i
    rw [hj] at h
    exact h
  by_cases h08 : j.val < 288
  · let i : Fin 32 := ⟨j.val-256, by omega⟩
    have hj : (⟨256+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck08 i
    rw [hj] at h
    exact h
  by_cases h09 : j.val < 320
  · let i : Fin 32 := ⟨j.val-288, by omega⟩
    have hj : (⟨288+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck09 i
    rw [hj] at h
    exact h
  by_cases h10 : j.val < 352
  · let i : Fin 32 := ⟨j.val-320, by omega⟩
    have hj : (⟨320+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck10 i
    rw [hj] at h
    exact h
  by_cases h11 : j.val < 384
  · let i : Fin 32 := ⟨j.val-352, by omega⟩
    have hj : (⟨352+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck11 i
    rw [hj] at h
    exact h
  by_cases h12 : j.val < 416
  · let i : Fin 32 := ⟨j.val-384, by omega⟩
    have hj : (⟨384+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck12 i
    rw [hj] at h
    exact h
  by_cases h13 : j.val < 448
  · let i : Fin 32 := ⟨j.val-416, by omega⟩
    have hj : (⟨416+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck13 i
    rw [hj] at h
    exact h
  by_cases h14 : j.val < 480
  · let i : Fin 32 := ⟨j.val-448, by omega⟩
    have hj : (⟨448+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck14 i
    rw [hj] at h
    exact h
  by_cases h15 : j.val < 512
  · let i : Fin 32 := ⟨j.val-480, by omega⟩
    have hj : (⟨480+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck15 i
    rw [hj] at h
    exact h
  by_cases h16 : j.val < 544
  · let i : Fin 32 := ⟨j.val-512, by omega⟩
    have hj : (⟨512+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck16 i
    rw [hj] at h
    exact h
  by_cases h17 : j.val < 576
  · let i : Fin 32 := ⟨j.val-544, by omega⟩
    have hj : (⟨544+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck17 i
    rw [hj] at h
    exact h
  by_cases h18 : j.val < 608
  · let i : Fin 32 := ⟨j.val-576, by omega⟩
    have hj : (⟨576+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck18 i
    rw [hj] at h
    exact h
  by_cases h19 : j.val < 640
  · let i : Fin 32 := ⟨j.val-608, by omega⟩
    have hj : (⟨608+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck19 i
    rw [hj] at h
    exact h
  by_cases h20 : j.val < 672
  · let i : Fin 32 := ⟨j.val-640, by omega⟩
    have hj : (⟨640+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck20 i
    rw [hj] at h
    exact h
  by_cases h21 : j.val < 704
  · let i : Fin 32 := ⟨j.val-672, by omega⟩
    have hj : (⟨672+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck21 i
    rw [hj] at h
    exact h
  by_cases h22 : j.val < 736
  · let i : Fin 32 := ⟨j.val-704, by omega⟩
    have hj : (⟨704+i.val, by omega⟩ : Fin 759) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := generatedAxisGlobalPreferredMaskFastCheck22 i
    rw [hj] at h
    exact h
  let i : Fin 23 := ⟨j.val-736, by omega⟩
  have hj : (⟨736+i.val, by omega⟩ : Fin 759) = j := by
    apply Fin.ext
    dsimp only [i]
    omega
  have h := generatedAxisGlobalPreferredMaskFastCheck23 i
  rw [hj] at h
  exact h

/-- Every bounded original code lookup equals the complete original catalogue entry. -/
theorem generatedAxisGlobalPreferredMaskOctadCode_actual (j : Fin 759) :
    generatedAxisGlobalPreferredMaskOctadCode j = generatedAxisGlobalOctadCodeData j :=
  (generatedAxisGlobalPreferredMaskOctad_actual j).1

/-- Every bounded physical coordinate equals the complete original catalogue entry. -/
theorem generatedAxisGlobalPreferredMaskOctadCoordinate_actual (j : Fin 759) (k : Fin 8) :
    generatedAxisGlobalPreferredMaskOctadCoordinate j k = generatedAxisGlobalOctadCoordinatesData j k :=
  (generatedAxisGlobalPreferredMaskOctad_actual j).2 k

/-- The bounded full preferred-mask formula is the actual original mask for every dictionary label. -/
theorem generatedAxisGlobalPreferredShortMaskFast_actual (r : GriessShortIndex) :
    generatedAxisGlobalPreferredShortMaskFast r = generatedAxisGlobalShortMask r :=
  generatedAxisGlobalPreferredShortMaskFast_sound
    generatedAxisGlobalPreferredMaskOctadCode_actual generatedAxisGlobalPreferredMaskOctadCoordinate_actual r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
