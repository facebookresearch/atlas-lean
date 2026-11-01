/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort0Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShortPhaseFast

/-! Actual physical characters and original full Parker constants of monomial word0. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Full original preferred-Q phase bits for each outgoing target octad row. -/
def generatedFifthPermutationShort0PhaseMasks : Fin 56 → ℕ :=
  ![
    7608384715226507670, 0, 18446462598732906495, 281474976645120,
    18446462598732906495, 281474976645120, 18446462598732906495, 281474976645120,
    18446462598732906495, 281474976645120, 0, 7608384715226507670,
    0, 7608384715226507670, 7608434000728254870, 7608434000728254870,
    7608434000728254870, 7608434000728254870, 10838310072981296745, 10838310072981296745,
    10838310072981296745, 10838310072981296745, 7608384715226507670, 0,
    11067990149230401945, 7378753924479149670, 7608434000728254870, 10838310072981296745,
    7608434000728254870, 10838310072981296745, 7378753924479149670, 11067990149230401945,
    17298308644996116495, 17298308644996116495, 0, 0,
    0, 0, 1148435428713435120, 1148435428713435120,
    1148435428713435120, 1148435428713435120, 0, 0,
    0, 0, 17298308644996116495, 17298308644996116495,
    7378753924479149670, 11067990149230401945, 10838310072981296745, 7608434000728254870,
    10838310072981296745, 7608434000728254870, 11067990149230401945, 7378753924479149670
  ]

/-- The binary phase represented by the literal row mask. -/
def generatedFifthPermutationShort0Phase (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  golayBooleanCast ((generatedFifthPermutationShort0PhaseMasks j).testBit e.val)

/-- Normalized eight-coordinate character labels of the actual correction code. -/
def generatedFifthPermutationShort0Character : Fin 56 → Fin 64 :=
  ![
    15, 0, 48, 48, 48, 48, 48, 48, 48, 48, 0, 15, 0, 15,
    63, 63, 63, 63, 63, 63, 63, 63, 15, 0, 51, 51, 63, 63,
    63, 63, 51, 51, 12, 12, 0, 0, 0, 0, 12, 12, 12, 12,
    0, 0, 0, 0, 12, 12, 51, 51, 63, 63, 63, 63, 51, 51
  ]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check only eight actual normalized physical bits per family.
/-- The original physical code intersection has precisely this Walsh label. -/
theorem generatedFifth_permutation_short0_character_bits : ∀ j : Fin 56, ∀ z : Fin 8,
    trialityBinaryBit (generatedFifthPermutationShort0Character j) z =
      golayBooleanCast ((golayEncodedMask 9).testBit
        (generatedFifthEvenRootCoordinates j z).val) +
      golayBooleanCast ((golayEncodedMask 9).testBit
        (generatedFifthEvenRootCoordinates j 7).val) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Verify the literal finite signed character rows; no actual-Q expansion is repeated.
/-- Each cached full-phase row is its zero coordinate times its original Walsh character. -/
theorem generatedFifth_permutation_short0_character_row : ∀ j : Fin 56, ∀ e : Fin 64,
    nortonUIntegerSign (generatedFifthPermutationShort0Phase j e) =
      nortonUIntegerSign (generatedFifthPermutationShort0Phase j 0) *
        generatedFifthSignHadamardCache (generatedFifthPermutationShort0Character j) e := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check the genuine original Parker polynomial and correction constants once per family.
/-- The exact original preferred-Q constant equals the zero-sign cached coefficient. -/
theorem generatedFifth_permutation_short0_constant : ∀ j : Fin 56,
    generatedFifthMonomialPermutationModelPhase 0
        (golayLabelCoefficients (generatedFifthEvenRootCode j)) +
      generatedFifthSignFamilyConstant (generatedFifthMonomialPermutationTranslation 0)
        (golayLabelCoefficients (generatedFifthMonomialPermutationModulation 0)) j =
          generatedFifthPermutationShort0Phase j 0 := by
  decide +kernel

/-- The original full actual preferred-Q phase equals the cached binary value. -/
theorem generatedFifth_permutation_short0_actual_phase (j : Fin 56) (e : Fin 64) :
    generatedFifthMonomialPermutationShortPhase 0 (Sum.inr (j, e)) =
      generatedFifthPermutationShort0Phase j e := by
  have hn := generatedFifth_sign_negative_character_of_row
    (⟨9, by decide⟩ : Fin 2048) j (generatedFifthPermutationShort0Character j)
    (generatedFifthPermutationShort0Phase j)
    (generatedFifth_permutation_short0_character_bits j)
    (generatedFifth_permutation_short0_character_row j) e
  change generatedFifthSignNegativeCharacter (9 : Fin 4096) j e =
    generatedFifthPermutationShort0Phase j e +
      generatedFifthPermutationShort0Phase j 0 at hn
  rw [generatedFifth_permutation_short_phase_formula, generatedFifth_permutation_short0_constant]
  rw [show generatedFifthMonomialPermutationTranslation 0 = (9 : Fin 4096) by decide +kernel]
  rw [hn]
  rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
