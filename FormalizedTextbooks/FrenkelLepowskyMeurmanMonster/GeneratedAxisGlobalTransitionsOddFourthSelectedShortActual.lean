/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMiddlePairingFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck00_00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck00_01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck00_02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck00_03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck00_04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck00_05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck00_06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck00_07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck00_08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck00_09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck01_00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck01_01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck01_02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck01_03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck01_04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck01_05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck01_06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck01_07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck01_08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck01_09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck02_00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck02_01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck02_02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck02_03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck02_04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck02_05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck02_06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck02_07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck02_08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck02_09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck03_00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck03_01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck03_02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck03_03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck03_04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck03_05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck03_06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck03_07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck03_08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCheck03_09

/-! Complete original selected preferred-Q certificates for all four actual Fourth frames. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- All complete selected original binary masks and central phases are kernel checked. -/
theorem generatedAxisGlobalOddFourthSelectedShortMasks_checked (k : Fin 4) (j : Fin 4584) :
    generatedAxisGlobalQMaskVector (generatedAxisGlobalOddFourthInverseMaskColumns k)
      (generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedTarget j)) =
        generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedSource k j) ∧
    (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalOddFourthInverseMaskRows k)
      (generatedAxisGlobalOddFourthInverseMaskCoefficients k)
      (generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedTarget j))).testBit 0
      then (1 : ZMod 2) else 0) = generatedAxisGlobalOddFourthSelectedPhase k j := by
  fin_cases k
  · by_cases h00 : j.val < 552
    · let i : Fin 552 := ⟨j.val-0, by omega⟩
      have hj : (⟨0+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_00_00 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_00_00 i)
      rw [hj] at h
      exact h
    by_cases h01 : j.val < 1000
    · let i : Fin 448 := ⟨j.val-552, by omega⟩
      have hj : (⟨552+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_00_01 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_00_01 i)
      rw [hj] at h
      exact h
    by_cases h02 : j.val < 1448
    · let i : Fin 448 := ⟨j.val-1000, by omega⟩
      have hj : (⟨1000+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_00_02 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_00_02 i)
      rw [hj] at h
      exact h
    by_cases h03 : j.val < 1896
    · let i : Fin 448 := ⟨j.val-1448, by omega⟩
      have hj : (⟨1448+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_00_03 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_00_03 i)
      rw [hj] at h
      exact h
    by_cases h04 : j.val < 2344
    · let i : Fin 448 := ⟨j.val-1896, by omega⟩
      have hj : (⟨1896+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_00_04 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_00_04 i)
      rw [hj] at h
      exact h
    by_cases h05 : j.val < 2792
    · let i : Fin 448 := ⟨j.val-2344, by omega⟩
      have hj : (⟨2344+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_00_05 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_00_05 i)
      rw [hj] at h
      exact h
    by_cases h06 : j.val < 3240
    · let i : Fin 448 := ⟨j.val-2792, by omega⟩
      have hj : (⟨2792+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_00_06 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_00_06 i)
      rw [hj] at h
      exact h
    by_cases h07 : j.val < 3688
    · let i : Fin 448 := ⟨j.val-3240, by omega⟩
      have hj : (⟨3240+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_00_07 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_00_07 i)
      rw [hj] at h
      exact h
    by_cases h08 : j.val < 4136
    · let i : Fin 448 := ⟨j.val-3688, by omega⟩
      have hj : (⟨3688+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_00_08 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_00_08 i)
      rw [hj] at h
      exact h
    let i : Fin 448 := ⟨j.val-4136, by omega⟩
    have hj : (⟨4136+i.val, by omega⟩ : Fin 4584) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_00_09 i)
      (generatedAxisGlobalOddFourthSelectedShortPhase_00_09 i)
    rw [hj] at h
    exact h
  · by_cases h00 : j.val < 552
    · let i : Fin 552 := ⟨j.val-0, by omega⟩
      have hj : (⟨0+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_01_00 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_01_00 i)
      rw [hj] at h
      exact h
    by_cases h01 : j.val < 1000
    · let i : Fin 448 := ⟨j.val-552, by omega⟩
      have hj : (⟨552+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_01_01 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_01_01 i)
      rw [hj] at h
      exact h
    by_cases h02 : j.val < 1448
    · let i : Fin 448 := ⟨j.val-1000, by omega⟩
      have hj : (⟨1000+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_01_02 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_01_02 i)
      rw [hj] at h
      exact h
    by_cases h03 : j.val < 1896
    · let i : Fin 448 := ⟨j.val-1448, by omega⟩
      have hj : (⟨1448+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_01_03 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_01_03 i)
      rw [hj] at h
      exact h
    by_cases h04 : j.val < 2344
    · let i : Fin 448 := ⟨j.val-1896, by omega⟩
      have hj : (⟨1896+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_01_04 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_01_04 i)
      rw [hj] at h
      exact h
    by_cases h05 : j.val < 2792
    · let i : Fin 448 := ⟨j.val-2344, by omega⟩
      have hj : (⟨2344+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_01_05 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_01_05 i)
      rw [hj] at h
      exact h
    by_cases h06 : j.val < 3240
    · let i : Fin 448 := ⟨j.val-2792, by omega⟩
      have hj : (⟨2792+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_01_06 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_01_06 i)
      rw [hj] at h
      exact h
    by_cases h07 : j.val < 3688
    · let i : Fin 448 := ⟨j.val-3240, by omega⟩
      have hj : (⟨3240+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_01_07 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_01_07 i)
      rw [hj] at h
      exact h
    by_cases h08 : j.val < 4136
    · let i : Fin 448 := ⟨j.val-3688, by omega⟩
      have hj : (⟨3688+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_01_08 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_01_08 i)
      rw [hj] at h
      exact h
    let i : Fin 448 := ⟨j.val-4136, by omega⟩
    have hj : (⟨4136+i.val, by omega⟩ : Fin 4584) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_01_09 i)
      (generatedAxisGlobalOddFourthSelectedShortPhase_01_09 i)
    rw [hj] at h
    exact h
  · by_cases h00 : j.val < 552
    · let i : Fin 552 := ⟨j.val-0, by omega⟩
      have hj : (⟨0+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_02_00 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_02_00 i)
      rw [hj] at h
      exact h
    by_cases h01 : j.val < 1000
    · let i : Fin 448 := ⟨j.val-552, by omega⟩
      have hj : (⟨552+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_02_01 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_02_01 i)
      rw [hj] at h
      exact h
    by_cases h02 : j.val < 1448
    · let i : Fin 448 := ⟨j.val-1000, by omega⟩
      have hj : (⟨1000+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_02_02 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_02_02 i)
      rw [hj] at h
      exact h
    by_cases h03 : j.val < 1896
    · let i : Fin 448 := ⟨j.val-1448, by omega⟩
      have hj : (⟨1448+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_02_03 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_02_03 i)
      rw [hj] at h
      exact h
    by_cases h04 : j.val < 2344
    · let i : Fin 448 := ⟨j.val-1896, by omega⟩
      have hj : (⟨1896+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_02_04 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_02_04 i)
      rw [hj] at h
      exact h
    by_cases h05 : j.val < 2792
    · let i : Fin 448 := ⟨j.val-2344, by omega⟩
      have hj : (⟨2344+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_02_05 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_02_05 i)
      rw [hj] at h
      exact h
    by_cases h06 : j.val < 3240
    · let i : Fin 448 := ⟨j.val-2792, by omega⟩
      have hj : (⟨2792+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_02_06 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_02_06 i)
      rw [hj] at h
      exact h
    by_cases h07 : j.val < 3688
    · let i : Fin 448 := ⟨j.val-3240, by omega⟩
      have hj : (⟨3240+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_02_07 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_02_07 i)
      rw [hj] at h
      exact h
    by_cases h08 : j.val < 4136
    · let i : Fin 448 := ⟨j.val-3688, by omega⟩
      have hj : (⟨3688+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_02_08 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_02_08 i)
      rw [hj] at h
      exact h
    let i : Fin 448 := ⟨j.val-4136, by omega⟩
    have hj : (⟨4136+i.val, by omega⟩ : Fin 4584) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_02_09 i)
      (generatedAxisGlobalOddFourthSelectedShortPhase_02_09 i)
    rw [hj] at h
    exact h
  · by_cases h00 : j.val < 552
    · let i : Fin 552 := ⟨j.val-0, by omega⟩
      have hj : (⟨0+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_03_00 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_03_00 i)
      rw [hj] at h
      exact h
    by_cases h01 : j.val < 1000
    · let i : Fin 448 := ⟨j.val-552, by omega⟩
      have hj : (⟨552+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_03_01 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_03_01 i)
      rw [hj] at h
      exact h
    by_cases h02 : j.val < 1448
    · let i : Fin 448 := ⟨j.val-1000, by omega⟩
      have hj : (⟨1000+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_03_02 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_03_02 i)
      rw [hj] at h
      exact h
    by_cases h03 : j.val < 1896
    · let i : Fin 448 := ⟨j.val-1448, by omega⟩
      have hj : (⟨1448+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_03_03 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_03_03 i)
      rw [hj] at h
      exact h
    by_cases h04 : j.val < 2344
    · let i : Fin 448 := ⟨j.val-1896, by omega⟩
      have hj : (⟨1896+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_03_04 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_03_04 i)
      rw [hj] at h
      exact h
    by_cases h05 : j.val < 2792
    · let i : Fin 448 := ⟨j.val-2344, by omega⟩
      have hj : (⟨2344+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_03_05 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_03_05 i)
      rw [hj] at h
      exact h
    by_cases h06 : j.val < 3240
    · let i : Fin 448 := ⟨j.val-2792, by omega⟩
      have hj : (⟨2792+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_03_06 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_03_06 i)
      rw [hj] at h
      exact h
    by_cases h07 : j.val < 3688
    · let i : Fin 448 := ⟨j.val-3240, by omega⟩
      have hj : (⟨3240+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_03_07 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_03_07 i)
      rw [hj] at h
      exact h
    by_cases h08 : j.val < 4136
    · let i : Fin 448 := ⟨j.val-3688, by omega⟩
      have hj : (⟨3688+i.val, by omega⟩ : Fin 4584) = j := by
        apply Fin.ext
        dsimp only [i]
        omega
      have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_03_08 i)
        (generatedAxisGlobalOddFourthSelectedShortPhase_03_08 i)
      rw [hj] at h
      exact h
    let i : Fin 448 := ⟨j.val-4136, by omega⟩
    have hj : (⟨4136+i.val, by omega⟩ : Fin 4584) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have h := And.intro (generatedAxisGlobalOddFourthSelectedShortBinary_03_09 i)
      (generatedAxisGlobalOddFourthSelectedShortPhase_03_09 i)
    rw [hj] at h
    exact h

/-- Every required preferred-Q inverse image is the entire actual original image. -/
theorem generatedAxisGlobalOddFourthSelectedInverseQ_unconditional (k : Fin 4) (j : Fin 4584) :
    spinConjugation ((generatedAxisGlobalOddFourthComparisonFiber k)⁻¹).val.1
      (griessShortQ (generatedAxisGlobalOddFourthSelectedTarget j)) =
      qCentral (generatedAxisGlobalOddFourthSelectedPhase k j) *
        griessShortQ (generatedAxisGlobalOddFourthSelectedSource k j) :=
  generatedAxisGlobalOddFourthSelectedInverseQ_actual k j
    (generatedAxisGlobalOddFourthSelectedShortMasks_checked k j).1
    (generatedAxisGlobalOddFourthSelectedShortMasks_checked k j).2

/-- Every required genuine framed short coordinate equals its original signed rational source coefficient. -/
theorem generatedAxisGlobalOddFourthSelectedShortQ_unconditional (k : Fin 4) (j : Fin 4584) :
    generatedAxisGlobalOddFourthFramedShort k (generatedAxisGlobalOddFourthSelectedTarget j) =
      generatedAxisGlobalOddFourthSelectedShortQ k j :=
  generatedAxisGlobalOddFourthSelectedShortQ_actual k j
    (generatedAxisGlobalOddFourthSelectedInverseQ_unconditional k j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
