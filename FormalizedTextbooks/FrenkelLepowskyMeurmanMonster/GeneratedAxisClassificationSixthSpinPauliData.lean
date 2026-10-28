/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddSpinStates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMasks

/-! Twelve original Pauli stabilizers transported through the genuine sixth local word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators

/-- Full translation, modulation and central signs at every original spin-word stage. -/
def generatedSixthSpinPauliCache : Fin 12 → Fin 9 → Q :=
![
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 1) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 241) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 14)
        (golayLabelCoefficients 241) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 14)
        (golayLabelCoefficients 144) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1008)
        (golayLabelCoefficients 865) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2966)
        (golayLabelCoefficients 64) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 912)
        (golayLabelCoefficients 1094) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 110)
        (golayLabelCoefficients 1752) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2151)
        (golayLabelCoefficients 1753) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 2) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 1075) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2051)
        (golayLabelCoefficients 1075) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1267)
        (golayLabelCoefficients 797) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1440)
        (golayLabelCoefficients 703) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1180)
        (golayLabelCoefficients 223) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 159)
        (golayLabelCoefficients 2259) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 460)
        (golayLabelCoefficients 2078) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1473)
        (golayLabelCoefficients 2066) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 4) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 355) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3)
        (golayLabelCoefficients 355) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3315)
        (golayLabelCoefficients 1143) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3488)
        (golayLabelCoefficients 1752) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3228)
        (golayLabelCoefficients 1343) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2207)
        (golayLabelCoefficients 2355) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2508)
        (golayLabelCoefficients 2558) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1473)
        (golayLabelCoefficients 3570) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 8) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 659) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3)
        (golayLabelCoefficients 659) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3315)
        (golayLabelCoefficients 1808) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3488)
        (golayLabelCoefficients 1471) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3228)
        (golayLabelCoefficients 1833) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2201)
        (golayLabelCoefficients 2853) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3636)
        (golayLabelCoefficients 2847) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1599)
        (golayLabelCoefficients 1812) 0],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 16) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 1040) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 1040) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 225) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 738) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 79) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 15)
        (golayLabelCoefficients 1103) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 348)
        (golayLabelCoefficients 1166) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2385)
        (golayLabelCoefficients 1154) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 32) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 48) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 48) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 1056) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 1359) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 1096) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2055)
        (golayLabelCoefficients 1096) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3412)
        (golayLabelCoefficients 1166) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2385)
        (golayLabelCoefficients 2181) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 64) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 1152) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 1152) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 1073) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 1885) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 1127) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2056)
        (golayLabelCoefficients 103) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3080)
        (golayLabelCoefficients 865) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 14)
        (golayLabelCoefficients 3942) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 128) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 192) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 192) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 1088) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 1582) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 782) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1)
        (golayLabelCoefficients 782) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 684)
        (golayLabelCoefficients 337) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 686)
        (golayLabelCoefficients 349) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 256) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 779) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 4)
        (golayLabelCoefficients 779) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2316)
        (golayLabelCoefficients 938) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2111)
        (golayLabelCoefficients 6) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3810)
        (golayLabelCoefficients 192) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 736)
        (golayLabelCoefficients 3277) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 45)
        (golayLabelCoefficients 3474) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3117)
        (golayLabelCoefficients 3472) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 512) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 12) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 12)
        (golayLabelCoefficients 12) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 768)
        (golayLabelCoefficients 240) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 254)
        (golayLabelCoefficients 0) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 912)
        (golayLabelCoefficients 768) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 912)
        (golayLabelCoefficients 768) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 110)
        (golayLabelCoefficients 1008) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 96)
        (golayLabelCoefficients 1009) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 1024) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 1265) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2062)
        (golayLabelCoefficients 1265) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2062)
        (golayLabelCoefficients 1121) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3056)
        (golayLabelCoefficients 1181) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 918)
        (golayLabelCoefficients 1062) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2966)
        (golayLabelCoefficients 1056) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3990)
        (golayLabelCoefficients 1609) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2969)
        (golayLabelCoefficients 2639) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 0) 1,
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
def generatedSixthSpinPauliInitial (j : Fin 12) : Q := generatedSixthSpinPauliCache j 0

set_option maxHeartbeats 4000000 in
-- All twelve initial operators retain their prescribed two-point state parameters.
/-- The twelve original generators fix the genuine initial Hadamard state. -/
theorem generatedSixth_spin_pauli_initial_parameters : ∀ j : Fin 12,
    generatedOddSpinLow (spinTranslation (generatedSixthSpinPauliInitial j)) = 0 ∧
    spinModulation (generatedSixthSpinPauliInitial j) 11 + 1 = 1 ∧
    generatedOddSpinOutputSign (generatedSixthSpinPauliInitial j) = 0 := by
  decide +kernel

/-- Every initial Pauli generator genuinely fixes the original odd-axis spin state. -/
theorem generatedSixth_spin_pauli_initial_fixed (j : Fin 12) :
    spinRepresentation (generatedSixthSpinPauliInitial j) (generatedOddSpinState 0 1 0) =
      generatedOddSpinState 0 1 0 := by
  change spinOperator (generatedSixthSpinPauliInitial j) _ = _
  rw [generatedOddSpinState_pauli]
  rcases generatedSixth_spin_pauli_initial_parameters j with ⟨ha, hb, hc⟩
  rw [ha, hb, hc]

/-- Nine independent translation columns among the twelve genuine final Pauli elements. -/
def generatedSixthSpinPauliIndependent : Fin 9 → Fin 12 := ![0,1,3,4,6,7,8,9,11]

/-- Literal final translation masks for the selected nine original Pauli elements. -/
def generatedSixthSpinPauliTranslationMask : Fin 9 → ℕ := ![2151,1473,1599,2385,14,686,3117,96,3058]

/-- A binary left inverse for the original nine translation columns. -/
def generatedSixthSpinPauliLeftInverseMask : Fin 9 → ℕ := ![12,27,267,493,414,109,240,332,246]

/-- The genuine binary translation matrix read from the literal masks. -/
def generatedSixthSpinPauliTranslationMatrix : Matrix (Fin 12) (Fin 9) (ZMod 2) :=
  fun i j => monsterCo1GeometryBinaryMaskDecode (generatedSixthSpinPauliTranslationMask j) i

/-- The literal binary left inverse acts on the original twelve spin coordinates. -/
def generatedSixthSpinPauliLeftInverse : Matrix (Fin 9) (Fin 12) (ZMod 2) :=
  fun i j => monsterCo1GeometryBinaryMaskDecode (generatedSixthSpinPauliLeftInverseMask i) j

set_option maxHeartbeats 2000000 in
-- Check all 81 matrix product entries, each a sum on the original twelve spin coordinates.
/-- The selected nine actual translation columns are linearly independent. -/
theorem generatedSixth_spin_pauli_left_inverse :
    generatedSixthSpinPauliLeftInverse * generatedSixthSpinPauliTranslationMatrix = 1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
