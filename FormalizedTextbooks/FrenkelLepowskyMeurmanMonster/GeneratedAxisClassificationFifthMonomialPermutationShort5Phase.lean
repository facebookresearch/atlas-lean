/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort5Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShortPhaseFast

/-! Actual physical characters and original full Parker constants of monomial word5. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Full original preferred-Q phase bits for each outgoing target octad row. -/
def generatedFifthPermutationShort5PhaseMasks : Fin 56 → ℕ :=
  ![
    1148435428713435120, 6510615555426900570, 11915017571648494245, 6148914692668172970,
    14757395256390660915, 14068333999483468995, 6531726502061057370, 6148914692668172970,
    14757395256390660915, 4378410074226082620, 14106333701151145020, 4340559386448706620,
    7608384715226507670, 6172933524171347370, 12297735557480819370, 14757226373981654220,
    12297735557480819370, 3689517699727897395, 12297735557480819370, 3689517699727897395,
    6149008516228732245, 3689517699727897395, 281474976645120, 4340410370284600380,
    17361393120864891120, 17361393120864891120, 6149008516228732245, 11914935430398977370,
    4378557928475212995, 14757226373981654220, 10850976253656798870, 10850976253656798870,
    6172933524171347370, 6172933524171347370, 1148681856222171120, 281474976645120,
    7378753924479149670, 7608434000728254870, 14714161359684946995, 14714161359684946995,
    12273810549538204245, 12273810549538204245, 17298062217487380495, 281474976645120,
    7378753924479149670, 10838310072981296745, 3732582714024604620, 3732582714024604620,
    7595767820052752745, 10850976253656798870, 14757226373981654220, 4378557928475212995,
    11914935430398977370, 6149008516228732245, 17361393120864891120, 1085350952844660495
  ]

/-- The binary phase represented by the literal row mask. -/
def generatedFifthPermutationShort5Phase (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  golayBooleanCast ((generatedFifthPermutationShort5PhaseMasks j).testBit e.val)

/-- Normalized eight-coordinate character labels of the actual correction code. -/
def generatedFifthPermutationShort5Character : Fin 56 → Fin 64 :=
  ![
    12, 5, 45, 33, 34, 46, 45, 33, 34, 46, 25, 54, 15, 57,
    14, 13, 14, 13, 14, 13, 14, 13, 48, 6, 11, 11, 14, 2,
    1, 13, 8, 8, 57, 57, 60, 48, 51, 63, 58, 58, 57, 57,
    60, 48, 51, 63, 58, 58, 8, 8, 13, 1, 2, 14, 11, 11
  ]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check only eight actual normalized physical bits per family.
/-- The original physical code intersection has precisely this Walsh label. -/
theorem generatedFifth_permutation_short5_character_bits : ∀ j : Fin 56, ∀ z : Fin 8,
    trialityBinaryBit (generatedFifthPermutationShort5Character j) z =
      golayBooleanCast ((golayEncodedMask 917).testBit
        (generatedFifthEvenRootCoordinates j z).val) +
      golayBooleanCast ((golayEncodedMask 917).testBit
        (generatedFifthEvenRootCoordinates j 7).val) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Verify the literal finite signed character rows; no actual-Q expansion is repeated.
/-- Each cached full-phase row is its zero coordinate times its original Walsh character. -/
theorem generatedFifth_permutation_short5_character_row : ∀ j : Fin 56, ∀ e : Fin 64,
    nortonUIntegerSign (generatedFifthPermutationShort5Phase j e) =
      nortonUIntegerSign (generatedFifthPermutationShort5Phase j 0) *
        generatedFifthSignHadamardCache (generatedFifthPermutationShort5Character j) e := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check the genuine original Parker polynomial and correction constants once per family.
/-- The exact original preferred-Q constant equals the zero-sign cached coefficient. -/
theorem generatedFifth_permutation_short5_constant : ∀ j : Fin 56,
    generatedFifthMonomialPermutationModelPhase 5
        (golayLabelCoefficients (generatedFifthEvenRootCode j)) +
      generatedFifthSignFamilyConstant (generatedFifthMonomialPermutationTranslation 5)
        (golayLabelCoefficients (generatedFifthMonomialPermutationModulation 5)) j =
          generatedFifthPermutationShort5Phase j 0 := by
  decide +kernel

/-- The original full actual preferred-Q phase equals the cached binary value. -/
theorem generatedFifth_permutation_short5_actual_phase (j : Fin 56) (e : Fin 64) :
    generatedFifthMonomialPermutationShortPhase 5 (Sum.inr (j, e)) =
      generatedFifthPermutationShort5Phase j e := by
  have hn := generatedFifth_sign_negative_character_of_row
    (⟨917, by decide⟩ : Fin 2048) j (generatedFifthPermutationShort5Character j)
    (generatedFifthPermutationShort5Phase j)
    (generatedFifth_permutation_short5_character_bits j)
    (generatedFifth_permutation_short5_character_row j) e
  change generatedFifthSignNegativeCharacter (917 : Fin 4096) j e =
    generatedFifthPermutationShort5Phase j e +
      generatedFifthPermutationShort5Phase j 0 at hn
  rw [generatedFifth_permutation_short_phase_formula, generatedFifth_permutation_short5_constant]
  rw [show generatedFifthMonomialPermutationTranslation 5 = (917 : Fin 4096) by decide +kernel]
  rw [hn]
  rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
