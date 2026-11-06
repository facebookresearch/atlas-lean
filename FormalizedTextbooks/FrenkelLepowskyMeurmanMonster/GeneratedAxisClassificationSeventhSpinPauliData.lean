/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhQConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddSpinStates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMasks

/-! Twelve original Pauli stabilizers transported through the genuine seventh local word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators

/-- Full translation, modulation and central signs at every original spin-word stage. -/
def generatedSeventhSpinPauliCache : Fin 12 → Fin 8 → Q :=
![
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 14)
      (golayLabelCoefficients 1) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 14)
      (golayLabelCoefficients 240) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1008)
      (golayLabelCoefficients 0) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2966)
      (golayLabelCoefficients 1798) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2966)
      (golayLabelCoefficients 768) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3990)
      (golayLabelCoefficients 775) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 920)
      (golayLabelCoefficients 3841) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 2) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 13)
      (golayLabelCoefficients 2) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3325)
      (golayLabelCoefficients 828) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3664)
      (golayLabelCoefficients 12) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1802)
      (golayLabelCoefficients 2039) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2824)
      (golayLabelCoefficients 4093) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3318)
      (golayLabelCoefficients 3846) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3318)
      (golayLabelCoefficients 768) 0],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 4) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 11)
      (golayLabelCoefficients 4) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1791)
      (golayLabelCoefficients 913) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1377)
      (golayLabelCoefficients 12) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 494)
      (golayLabelCoefficients 1633) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2542)
      (golayLabelCoefficients 1632) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2851)
      (golayLabelCoefficients 1373) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2850)
      (golayLabelCoefficients 350) 0],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 8) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 7)
      (golayLabelCoefficients 8) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1535)
      (golayLabelCoefficients 865) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1439)
      (golayLabelCoefficients 12) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 638)
      (golayLabelCoefficients 1377) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2686)
      (golayLabelCoefficients 1376) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2893)
      (golayLabelCoefficients 1709) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2882)
      (golayLabelCoefficients 687) 0],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 16) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 16) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1040) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1310) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1065) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2057)
      (golayLabelCoefficients 1065) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3748)
      (golayLabelCoefficients 1055) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2735)
      (golayLabelCoefficients 2068) 0],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 32) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 32) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 48) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 81) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 97) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 14)
      (golayLabelCoefficients 97) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1008)
      (golayLabelCoefficients 145) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1022)
      (golayLabelCoefficients 145) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 64) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 64) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1152) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1679) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 783) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 15)
      (golayLabelCoefficients 783) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 348)
      (golayLabelCoefficients 673) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 350)
      (golayLabelCoefficients 685) 0],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 128) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 128) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 192) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 161) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 14)
      (golayLabelCoefficients 1) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1008)
      (golayLabelCoefficients 1008) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1008)
      (golayLabelCoefficients 1008) 0],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 256) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 256) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 779) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 10) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1696) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
      (golayLabelCoefficients 1696) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
      (golayLabelCoefficients 1999) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2063)
      (golayLabelCoefficients 975) 0],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 512) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 512) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 12) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 12) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1008) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1008) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 241) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 14)
      (golayLabelCoefficients 241) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1024) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
      (golayLabelCoefficients 1024) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
      (golayLabelCoefficients 1265) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
      (golayLabelCoefficients 2044) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
      (golayLabelCoefficients 1126) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2054)
      (golayLabelCoefficients 102) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 4088)
      (golayLabelCoefficients 145) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1022)
      (golayLabelCoefficients 3222) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
      (golayLabelCoefficients 0) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1024) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1265) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 2044) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1126) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2054)
      (golayLabelCoefficients 1126) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 4088)
      (golayLabelCoefficients 1181) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3058)
      (golayLabelCoefficients 2202) 1]]

/-- The actual initial Pauli generators, before the original local word. -/
def generatedSeventhSpinPauliInitial (j : Fin 12) : Q := generatedSeventhSpinPauliCache j 0

set_option maxHeartbeats 4000000 in
-- All twelve initial operators retain their prescribed two-point state parameters.
/-- The twelve original generators fix the genuine initial Hadamard state. -/
theorem generatedSeventh_spin_pauli_initial_parameters : ∀ j : Fin 12,
    generatedOddSpinLow (spinTranslation (generatedSeventhSpinPauliInitial j)) = 0 ∧
    spinModulation (generatedSeventhSpinPauliInitial j) 11 + 1 = 1 ∧
    generatedOddSpinOutputSign (generatedSeventhSpinPauliInitial j) = 0 := by
  decide +kernel

/-- Every initial Pauli generator genuinely fixes the original odd-axis spin state. -/
theorem generatedSeventh_spin_pauli_initial_fixed (j : Fin 12) :
    spinRepresentation (generatedSeventhSpinPauliInitial j) (generatedOddSpinState 0 1 0) =
      generatedOddSpinState 0 1 0 := by
  change spinOperator (generatedSeventhSpinPauliInitial j) _ = _
  rw [generatedOddSpinState_pauli]
  rcases generatedSeventh_spin_pauli_initial_parameters j with ⟨ha, hb, hc⟩
  rw [ha, hb, hc]

/-- Nine independent translation columns among the twelve genuine final Pauli elements. -/
def generatedSeventhSpinPauliIndependent : Fin 9 → Fin 12 := ![0,1,2,3,4,5,6,7,11]

/-- Literal final translation masks for the selected nine original Pauli elements. -/
def generatedSeventhSpinPauliTranslationMask : Fin 9 → ℕ :=
  ![920,3318,2850,2882,2735,1022,350,1008,3058]

/-- A binary left inverse for the original nine translation columns. -/
def generatedSeventhSpinPauliLeftInverseMask : Fin 9 → ℕ := ![492,480,332,444,1,372,145,271,246]

/-- The genuine binary translation matrix read from the literal masks. -/
def generatedSeventhSpinPauliTranslationMatrix : Matrix (Fin 12) (Fin 9) (ZMod 2) :=
  fun i j => monsterCo1GeometryBinaryMaskDecode (generatedSeventhSpinPauliTranslationMask j) i

/-- The literal binary left inverse acts on the original twelve spin coordinates. -/
def generatedSeventhSpinPauliLeftInverse : Matrix (Fin 9) (Fin 12) (ZMod 2) :=
  fun i j => monsterCo1GeometryBinaryMaskDecode (generatedSeventhSpinPauliLeftInverseMask i) j

set_option maxHeartbeats 2000000 in
-- Check all 81 matrix product entries, each a sum on the original twelve spin coordinates.
/-- The selected nine actual translation columns are linearly independent. -/
theorem generatedSeventh_spin_pauli_left_inverse :
    generatedSeventhSpinPauliLeftInverse * generatedSeventhSpinPauliTranslationMatrix = 1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
