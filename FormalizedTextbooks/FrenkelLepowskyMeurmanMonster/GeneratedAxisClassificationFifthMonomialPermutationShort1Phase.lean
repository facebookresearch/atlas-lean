/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort1Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShortPhaseFast

/-! Actual physical characters and original full Parker constants of monomial word1. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Full original preferred-Q phase bits for each outgoing target octad row. -/
def generatedFifthPermutationShort1PhaseMasks : Fin 56 → ℕ :=
  ![
    0, 4340410370284600380, 3732415143318664140, 4340410370284600380,
    4340410370284600380, 3732415143318664140, 3732415143318664140, 4340410370284600380,
    4340410370284600380, 3732415143318664140, 11936045732788001370, 3732415143318664140,
    1148435428713435120, 6510698342184737370, 3689348814741910323, 4378410071969971395,
    3689348814741910323, 4378410071969971395, 4378410071969971395, 3689348814741910323,
    4378410071969971395, 3689348814741910323, 7608434000728254870, 6510698342184737370,
    3689348814741910323, 3689348814741910323, 11053691001366813030, 10851025925711500950,
    17361641481138401520, 18374966859414961920, 6148914691236517205, 6148914691236517205,
    0, 0, 6172840429334713770, 6510615555426900570,
    4340410370284600380, 3732415143318664140, 7378697629483820646, 7378697629483820646,
    281474976645120, 281474976645120, 6172933524171347370, 6510698342184737370,
    4340559386448706620, 3732582714024604620, 7378753924479149670, 7378753924479149670,
    6148914691236517205, 6148914691236517205, 18374966859414961920, 17361641481138401520,
    10851025925711500950, 11053691001366813030, 3689348814741910323, 3689348814741910323
  ]

/-- The binary phase represented by the literal row mask. -/
def generatedFifthPermutationShort1Phase (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  golayBooleanCast ((generatedFifthPermutationShort1PhaseMasks j).testBit e.val)

/-- Normalized eight-coordinate character labels of the actual correction code. -/
def generatedFifthPermutationShort1Character : Fin 56 → Fin 64 :=
  ![
    0, 6, 10, 6, 6, 10, 10, 6, 6, 10, 42, 10, 12, 53,
    61, 49, 61, 49, 49, 61, 49, 61, 63, 53, 61, 61, 52, 56,
    59, 55, 62, 62, 0, 0, 9, 5, 6, 10, 3, 3, 48, 48,
    57, 53, 54, 58, 51, 51, 62, 62, 55, 59, 56, 52, 61, 61
  ]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check only eight actual normalized physical bits per family.
/-- The original physical code intersection has precisely this Walsh label. -/
theorem generatedFifth_permutation_short1_character_bits : ∀ j : Fin 56, ∀ z : Fin 8,
    trialityBinaryBit (generatedFifthPermutationShort1Character j) z =
      golayBooleanCast ((golayEncodedMask 704).testBit
        (generatedFifthEvenRootCoordinates j z).val) +
      golayBooleanCast ((golayEncodedMask 704).testBit
        (generatedFifthEvenRootCoordinates j 7).val) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Verify the literal finite signed character rows; no actual-Q expansion is repeated.
/-- Each cached full-phase row is its zero coordinate times its original Walsh character. -/
theorem generatedFifth_permutation_short1_character_row : ∀ j : Fin 56, ∀ e : Fin 64,
    nortonUIntegerSign (generatedFifthPermutationShort1Phase j e) =
      nortonUIntegerSign (generatedFifthPermutationShort1Phase j 0) *
        generatedFifthSignHadamardCache (generatedFifthPermutationShort1Character j) e := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check the genuine original Parker polynomial and correction constants once per family.
/-- The exact original preferred-Q constant equals the zero-sign cached coefficient. -/
theorem generatedFifth_permutation_short1_constant : ∀ j : Fin 56,
    generatedFifthMonomialPermutationModelPhase 1
        (golayLabelCoefficients (generatedFifthEvenRootCode j)) +
      generatedFifthSignFamilyConstant (generatedFifthMonomialPermutationTranslation 1)
        (golayLabelCoefficients (generatedFifthMonomialPermutationModulation 1)) j =
          generatedFifthPermutationShort1Phase j 0 := by
  decide +kernel

/-- The original full actual preferred-Q phase equals the cached binary value. -/
theorem generatedFifth_permutation_short1_actual_phase (j : Fin 56) (e : Fin 64) :
    generatedFifthMonomialPermutationShortPhase 1 (Sum.inr (j, e)) =
      generatedFifthPermutationShort1Phase j e := by
  have hn := generatedFifth_sign_negative_character_of_row
    (⟨704, by decide⟩ : Fin 2048) j (generatedFifthPermutationShort1Character j)
    (generatedFifthPermutationShort1Phase j)
    (generatedFifth_permutation_short1_character_bits j)
    (generatedFifth_permutation_short1_character_row j) e
  change generatedFifthSignNegativeCharacter (704 : Fin 4096) j e =
    generatedFifthPermutationShort1Phase j e +
      generatedFifthPermutationShort1Phase j 0 at hn
  rw [generatedFifth_permutation_short_phase_formula, generatedFifth_permutation_short1_constant]
  rw [show generatedFifthMonomialPermutationTranslation 1 = (704 : Fin 4096) by decide +kernel]
  rw [hn]
  rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
