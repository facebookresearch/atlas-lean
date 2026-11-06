/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShortPhaseFast

/-! Actual physical characters and original full Parker constants of monomial word2. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Full original preferred-Q phase bits for each outgoing target octad row. -/
def generatedFifthPermutationShort2PhaseMasks : Fin 56 → ℕ :=
  ![
    6510615555426900570, 0, 12297735558912431445, 6148914692668172970,
    14757226376558555955, 3689348817318890700, 12297829381041378645, 6149008514797120170,
    14757395256390660915, 3689517697150995660, 6172840429334713770, 14106333701151145020,
    1148435428713435120, 14106184689534581820, 14757395258967641292, 14757226373981654220,
    11914935430398977370, 11915017572901889370, 4378410071969971395, 4378557928475212995,
    6149008516228732245, 6148914691236517205, 10838310073733310870, 4340559386448706620,
    10851025925711500950, 7393053072342738585, 3689348814741910323, 14757395258967641292,
    6148914691236517205, 12297829382473034410, 71777214294589695, 17361641481138401520,
    6510615555426900570, 6172840429334713770, 0, 0,
    7378697629483820646, 7378697629483820646, 14714328930390887475, 14106333703424951235,
    11936045731524814245, 12273810549538204245, 281474976645120, 281474976645120,
    7378753924479149670, 7378753924479149670, 3732582714024604620, 4340559386448706620,
    7393108929244718745, 10850976253656798870, 14068186145234338620, 4378557928475212995,
    11914935430398977370, 6531808643310574245, 17361393120864891120, 72056498804490495
  ]

/-- The binary phase represented by the literal row mask. -/
def generatedFifthPermutationShort2Phase (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  golayBooleanCast ((generatedFifthPermutationShort2PhaseMasks j).testBit e.val)

/-- Normalized eight-coordinate character labels of the actual correction code. -/
def generatedFifthPermutationShort2Character : Fin 56 → Fin 64 :=
  ![
    5, 0, 17, 33, 18, 34, 33, 17, 34, 18, 9, 25, 12, 41,
    61, 13, 2, 50, 49, 1, 14, 62, 32, 54, 56, 52, 61, 61,
    62, 62, 55, 59, 5, 9, 0, 0, 3, 3, 10, 6, 53, 57,
    48, 48, 51, 51, 58, 54, 4, 8, 1, 1, 2, 2, 11, 7
  ]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check only eight actual normalized physical bits per family.
/-- The original physical code intersection has precisely this Walsh label. -/
theorem generatedFifth_permutation_short2_character_bits : ∀ j : Fin 56, ∀ z : Fin 8,
    trialityBinaryBit (generatedFifthPermutationShort2Character j) z =
      golayBooleanCast ((golayEncodedMask 801).testBit
        (generatedFifthEvenRootCoordinates j z).val) +
      golayBooleanCast ((golayEncodedMask 801).testBit
        (generatedFifthEvenRootCoordinates j 7).val) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Verify the literal finite signed character rows; no actual-Q expansion is repeated.
/-- Each cached full-phase row is its zero coordinate times its original Walsh character. -/
theorem generatedFifth_permutation_short2_character_row : ∀ j : Fin 56, ∀ e : Fin 64,
    nortonUIntegerSign (generatedFifthPermutationShort2Phase j e) =
      nortonUIntegerSign (generatedFifthPermutationShort2Phase j 0) *
        generatedFifthSignHadamardCache (generatedFifthPermutationShort2Character j) e := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check the genuine original Parker polynomial and correction constants once per family.
/-- The exact original preferred-Q constant equals the zero-sign cached coefficient. -/
theorem generatedFifth_permutation_short2_constant : ∀ j : Fin 56,
    generatedFifthMonomialPermutationModelPhase 2
        (golayLabelCoefficients (generatedFifthEvenRootCode j)) +
      generatedFifthSignFamilyConstant (generatedFifthMonomialPermutationTranslation 2)
        (golayLabelCoefficients (generatedFifthMonomialPermutationModulation 2)) j =
          generatedFifthPermutationShort2Phase j 0 := by
  decide +kernel

/-- The original full actual preferred-Q phase equals the cached binary value. -/
theorem generatedFifth_permutation_short2_actual_phase (j : Fin 56) (e : Fin 64) :
    generatedFifthMonomialPermutationShortPhase 2 (Sum.inr (j, e)) =
      generatedFifthPermutationShort2Phase j e := by
  have hn := generatedFifth_sign_negative_character_of_row
    (⟨801, by decide⟩ : Fin 2048) j (generatedFifthPermutationShort2Character j)
    (generatedFifthPermutationShort2Phase j)
    (generatedFifth_permutation_short2_character_bits j)
    (generatedFifth_permutation_short2_character_row j) e
  change generatedFifthSignNegativeCharacter (801 : Fin 4096) j e =
    generatedFifthPermutationShort2Phase j e +
      generatedFifthPermutationShort2Phase j 0 at hn
  rw [generatedFifth_permutation_short_phase_formula, generatedFifth_permutation_short2_constant]
  rw [show generatedFifthMonomialPermutationTranslation 2 = (801 : Fin 4096) by decide +kernel]
  rw [hn]
  rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
