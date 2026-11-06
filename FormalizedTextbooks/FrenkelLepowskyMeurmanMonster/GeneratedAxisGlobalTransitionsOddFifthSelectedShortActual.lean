/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck00_00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck00_01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck00_02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck00_03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck00_04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck00_05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck00_06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck00_07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck00_08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck01_00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck01_01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck01_02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck01_03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck01_04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck01_05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck01_06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck01_07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCheck01_08

/-! Every original selected preferred-Q image and central phase is checked for both full frames. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- All original binary and central images are checked for every selected preferred target. -/
theorem generatedAxisGlobalOddFifthSelectedShortMasks_checked (k : Fin 2) (j : Fin 4136) :
    generatedAxisGlobalQMaskVector (generatedAxisGlobalOddFifthInverseMaskColumns k)
      (generatedAxisGlobalShortMask (generatedAxisGlobalOddFifthSelectedTarget j)) =
        generatedAxisGlobalShortMask (generatedAxisGlobalOddFifthSelectedSource k j) ∧
    (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalOddFifthInverseMaskRows k)
      (generatedAxisGlobalOddFifthInverseMaskCoefficients k)
      (generatedAxisGlobalShortMask (generatedAxisGlobalOddFifthSelectedTarget j))).testBit 0
      then (1 : ZMod 2) else 0) = generatedAxisGlobalOddFifthSelectedPhase k j := by
  fin_cases k
  · by_cases h00 : j.val < 552
    · let i : Fin 552 := ⟨j.val-0, by omega⟩
      have hj : (⟨0+i.val, by omega⟩ : Fin 4136) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_00_00 i)
        (generatedAxisGlobalOddFifthSelectedShortPhase_00_00 i)
      rw [hj] at h
      exact h
    by_cases h01 : j.val < 1000
    · let i : Fin 448 := ⟨j.val-552, by omega⟩
      have hj : (⟨552+i.val, by omega⟩ : Fin 4136) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_00_01 i)
        (generatedAxisGlobalOddFifthSelectedShortPhase_00_01 i)
      rw [hj] at h
      exact h
    by_cases h02 : j.val < 1448
    · let i : Fin 448 := ⟨j.val-1000, by omega⟩
      have hj : (⟨1000+i.val, by omega⟩ : Fin 4136) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_00_02 i)
        (generatedAxisGlobalOddFifthSelectedShortPhase_00_02 i)
      rw [hj] at h
      exact h
    by_cases h03 : j.val < 1896
    · let i : Fin 448 := ⟨j.val-1448, by omega⟩
      have hj : (⟨1448+i.val, by omega⟩ : Fin 4136) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_00_03 i)
        (generatedAxisGlobalOddFifthSelectedShortPhase_00_03 i)
      rw [hj] at h
      exact h
    by_cases h04 : j.val < 2344
    · let i : Fin 448 := ⟨j.val-1896, by omega⟩
      have hj : (⟨1896+i.val, by omega⟩ : Fin 4136) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_00_04 i)
        (generatedAxisGlobalOddFifthSelectedShortPhase_00_04 i)
      rw [hj] at h
      exact h
    by_cases h05 : j.val < 2792
    · let i : Fin 448 := ⟨j.val-2344, by omega⟩
      have hj : (⟨2344+i.val, by omega⟩ : Fin 4136) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_00_05 i)
        (generatedAxisGlobalOddFifthSelectedShortPhase_00_05 i)
      rw [hj] at h
      exact h
    by_cases h06 : j.val < 3240
    · let i : Fin 448 := ⟨j.val-2792, by omega⟩
      have hj : (⟨2792+i.val, by omega⟩ : Fin 4136) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_00_06 i)
        (generatedAxisGlobalOddFifthSelectedShortPhase_00_06 i)
      rw [hj] at h
      exact h
    by_cases h07 : j.val < 3688
    · let i : Fin 448 := ⟨j.val-3240, by omega⟩
      have hj : (⟨3240+i.val, by omega⟩ : Fin 4136) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_00_07 i)
        (generatedAxisGlobalOddFifthSelectedShortPhase_00_07 i)
      rw [hj] at h
      exact h
    let i : Fin 448 := ⟨j.val-3688, by omega⟩
    have hj : (⟨3688+i.val, by omega⟩ : Fin 4136) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_00_08 i)
      (generatedAxisGlobalOddFifthSelectedShortPhase_00_08 i)
    rw [hj] at h
    exact h
  · by_cases h00 : j.val < 552
    · let i : Fin 552 := ⟨j.val-0, by omega⟩
      have hj : (⟨0+i.val, by omega⟩ : Fin 4136) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_01_00 i)
        (generatedAxisGlobalOddFifthSelectedShortPhase_01_00 i)
      rw [hj] at h
      exact h
    by_cases h01 : j.val < 1000
    · let i : Fin 448 := ⟨j.val-552, by omega⟩
      have hj : (⟨552+i.val, by omega⟩ : Fin 4136) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_01_01 i)
        (generatedAxisGlobalOddFifthSelectedShortPhase_01_01 i)
      rw [hj] at h
      exact h
    by_cases h02 : j.val < 1448
    · let i : Fin 448 := ⟨j.val-1000, by omega⟩
      have hj : (⟨1000+i.val, by omega⟩ : Fin 4136) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_01_02 i)
        (generatedAxisGlobalOddFifthSelectedShortPhase_01_02 i)
      rw [hj] at h
      exact h
    by_cases h03 : j.val < 1896
    · let i : Fin 448 := ⟨j.val-1448, by omega⟩
      have hj : (⟨1448+i.val, by omega⟩ : Fin 4136) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_01_03 i)
        (generatedAxisGlobalOddFifthSelectedShortPhase_01_03 i)
      rw [hj] at h
      exact h
    by_cases h04 : j.val < 2344
    · let i : Fin 448 := ⟨j.val-1896, by omega⟩
      have hj : (⟨1896+i.val, by omega⟩ : Fin 4136) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_01_04 i)
        (generatedAxisGlobalOddFifthSelectedShortPhase_01_04 i)
      rw [hj] at h
      exact h
    by_cases h05 : j.val < 2792
    · let i : Fin 448 := ⟨j.val-2344, by omega⟩
      have hj : (⟨2344+i.val, by omega⟩ : Fin 4136) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_01_05 i)
        (generatedAxisGlobalOddFifthSelectedShortPhase_01_05 i)
      rw [hj] at h
      exact h
    by_cases h06 : j.val < 3240
    · let i : Fin 448 := ⟨j.val-2792, by omega⟩
      have hj : (⟨2792+i.val, by omega⟩ : Fin 4136) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_01_06 i)
        (generatedAxisGlobalOddFifthSelectedShortPhase_01_06 i)
      rw [hj] at h
      exact h
    by_cases h07 : j.val < 3688
    · let i : Fin 448 := ⟨j.val-3240, by omega⟩
      have hj : (⟨3240+i.val, by omega⟩ : Fin 4136) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_01_07 i)
        (generatedAxisGlobalOddFifthSelectedShortPhase_01_07 i)
      rw [hj] at h
      exact h
    let i : Fin 448 := ⟨j.val-3688, by omega⟩
    have hj : (⟨3688+i.val, by omega⟩ : Fin 4136) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := And.intro (generatedAxisGlobalOddFifthSelectedShortBinary_01_08 i)
      (generatedAxisGlobalOddFifthSelectedShortPhase_01_08 i)
    rw [hj] at h
    exact h

/-- Every required preferred-Q inverse image is the entire actual original image. -/
theorem generatedAxisGlobalOddFifthSelectedInverseQ_unconditional (k : Fin 2) (j : Fin 4136) :
    spinConjugation ((generatedAxisGlobalOddFifthComparisonFiber k)⁻¹).val.1
      (griessShortQ (generatedAxisGlobalOddFifthSelectedTarget j)) =
      qCentral (generatedAxisGlobalOddFifthSelectedPhase k j) *
        griessShortQ (generatedAxisGlobalOddFifthSelectedSource k j) :=
  generatedAxisGlobalOddFifthSelectedInverseQ_actual k j
    (generatedAxisGlobalOddFifthSelectedShortMasks_checked k j).1
    (generatedAxisGlobalOddFifthSelectedShortMasks_checked k j).2

/-- Every required genuine framed short coordinate equals its original signed rational source coefficient. -/
theorem generatedAxisGlobalOddFifthSelectedShortQ_unconditional (k : Fin 2) (j : Fin 4136) :
    generatedAxisGlobalOddFifthFramedShort k (generatedAxisGlobalOddFifthSelectedTarget j) =
      generatedAxisGlobalOddFifthSelectedShortQ k j :=
  generatedAxisGlobalOddFifthSelectedShortQ_actual k j
    (generatedAxisGlobalOddFifthSelectedInverseQ_unconditional k j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
