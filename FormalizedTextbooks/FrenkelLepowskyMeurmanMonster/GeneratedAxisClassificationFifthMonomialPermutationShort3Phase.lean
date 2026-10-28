/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort3Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShortPhaseFast

/-! Actual physical characters and original full Parker constants of monomial word3. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Full original preferred-Q phase bits for each outgoing target octad row. -/
def generatedFifthPermutationShort3PhaseMasks : Fin 56 → ℕ :=
  ![
    6172933524171347370, 18446462598732906495, 6531726500807662245, 6531808643310574245,
    14068334001739580220, 14068186145234338620, 6531808643310574245, 6531726500807662245,
    14068186145234338620, 14068334001739580220, 14106333703424951235, 14106184689534581820,
    18446462598732906495, 14106333701151145020, 12297735558912431445, 6531726502061057370,
    14068333999483468995, 3689517697150995660, 12297735558912431445, 6531726502061057370,
    14068333999483468995, 3689517697150995660, 11068046443366737510, 14106333703424951235,
    1148681856222171120, 0, 12297735558912431445, 12297735558912431445,
    3689517697150995660, 3689517697150995660, 7378753924479149670, 7608384715226507670,
    6149008516228732245, 6531808643310574245, 7378697629483820646, 1148681856222171120,
    0, 7608434000728254870, 14068186145234338620, 14757226373981654220,
    6149008516228732245, 6531808643310574245, 1148681856222171120, 7378697629483820646,
    7608434000728254870, 0, 14068186145234338620, 14757226373981654220,
    0, 1148681856222171120, 6531726502061057370, 6531726502061057370,
    14068333999483468995, 14068333999483468995, 7608384715226507670, 7378753924479149670
  ]

/-- The binary phase represented by the literal row mask. -/
def generatedFifthPermutationShort3Phase (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  golayBooleanCast ((generatedFifthPermutationShort3PhaseMasks j).testBit e.val)

/-- Normalized eight-coordinate character labels of the actual correction code. -/
def generatedFifthPermutationShort3Character : Fin 56 → Fin 64 :=
  ![
    57, 48, 50, 2, 49, 1, 2, 50, 1, 49, 6, 41, 48, 25,
    17, 45, 46, 18, 17, 45, 46, 18, 28, 6, 60, 0, 17, 17,
    18, 18, 51, 15, 14, 2, 3, 60, 0, 63, 1, 13, 14, 2,
    60, 3, 63, 0, 1, 13, 0, 60, 45, 45, 46, 46, 15, 51
  ]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check only eight actual normalized physical bits per family.
/-- The original physical code intersection has precisely this Walsh label. -/
theorem generatedFifth_permutation_short3_character_bits : ∀ j : Fin 56, ∀ z : Fin 8,
    trialityBinaryBit (generatedFifthPermutationShort3Character j) z =
      golayBooleanCast ((golayEncodedMask 821).testBit
        (generatedFifthEvenRootCoordinates j z).val) +
      golayBooleanCast ((golayEncodedMask 821).testBit
        (generatedFifthEvenRootCoordinates j 7).val) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Verify the literal finite signed character rows; no actual-Q expansion is repeated.
/-- Each cached full-phase row is its zero coordinate times its original Walsh character. -/
theorem generatedFifth_permutation_short3_character_row : ∀ j : Fin 56, ∀ e : Fin 64,
    nortonUIntegerSign (generatedFifthPermutationShort3Phase j e) =
      nortonUIntegerSign (generatedFifthPermutationShort3Phase j 0) *
        generatedFifthSignHadamardCache (generatedFifthPermutationShort3Character j) e := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check the genuine original Parker polynomial and correction constants once per family.
/-- The exact original preferred-Q constant equals the zero-sign cached coefficient. -/
theorem generatedFifth_permutation_short3_constant : ∀ j : Fin 56,
    generatedFifthMonomialPermutationModelPhase 3
        (golayLabelCoefficients (generatedFifthEvenRootCode j)) +
      generatedFifthSignFamilyConstant (generatedFifthMonomialPermutationTranslation 3)
        (golayLabelCoefficients (generatedFifthMonomialPermutationModulation 3)) j =
          generatedFifthPermutationShort3Phase j 0 := by
  decide +kernel

/-- The original full actual preferred-Q phase equals the cached binary value. -/
theorem generatedFifth_permutation_short3_actual_phase (j : Fin 56) (e : Fin 64) :
    generatedFifthMonomialPermutationShortPhase 3 (Sum.inr (j, e)) =
      generatedFifthPermutationShort3Phase j e := by
  have hn := generatedFifth_sign_negative_character_of_row
    (⟨821, by decide⟩ : Fin 2048) j (generatedFifthPermutationShort3Character j)
    (generatedFifthPermutationShort3Phase j)
    (generatedFifth_permutation_short3_character_bits j)
    (generatedFifth_permutation_short3_character_row j) e
  change generatedFifthSignNegativeCharacter (821 : Fin 4096) j e =
    generatedFifthPermutationShort3Phase j e +
      generatedFifthPermutationShort3Phase j 0 at hn
  rw [generatedFifth_permutation_short_phase_formula, generatedFifth_permutation_short3_constant]
  rw [show generatedFifthMonomialPermutationTranslation 3 = (821 : Fin 4096) by decide +kernel]
  rw [hn]
  rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
