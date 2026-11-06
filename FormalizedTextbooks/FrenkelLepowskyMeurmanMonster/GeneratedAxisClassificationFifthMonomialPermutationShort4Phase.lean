/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort4Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShortPhaseFast

/-! Actual physical characters and original full Parker constants of monomial word4. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Full original preferred-Q phase bits for each outgoing target octad row. -/
def generatedFifthPermutationShort4PhaseMasks : Fin 56 → ℕ :=
  ![
    14106333703424951235, 12273903644374837845, 4340410370284600380, 14714161359684946995,
    12273903644374837845, 11936045731524814245, 4340559386448706620, 3732415143318664140,
    6172933524171347370, 11936128518282651045, 4340559384174969795, 6172933522750876245,
    12273903644374837845, 14106333703424951235, 6510615555426900570, 3732415143318664140,
    11936128518282651045, 3732415143318664140, 12273903644374837845, 4340410370284600380,
    12273903644374837845, 14106333703424951235, 18446744073709551615, 4340559384174969795,
    0, 17298308644996116495, 6510615555426900570, 6172840429334713770,
    14714328930390887475, 14106333703424951235, 10838359358483043945, 7378697629483820646,
    3689517697150995660, 14068186147490380995, 10850976254414711145, 7393108928392436070,
    72056494543077120, 17361393124654452495, 6531808642057217370, 12297735558912431445,
    3689348817318890700, 14068333999483468995, 10851025924953565545, 11053691000514504345,
    18374966855153418495, 17361641477348724495, 6531726502061057370, 12297829381041378645,
    7378697629483820646, 7608384715226507670, 4340410370284600380, 3732415143318664140,
    12273903644374837845, 11936128518282651045, 1148435428713435120, 0
  ]

/-- The binary phase represented by the literal row mask. -/
def generatedFifthPermutationShort4Phase (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  golayBooleanCast ((generatedFifthPermutationShort4PhaseMasks j).testBit e.val)

/-- Normalized eight-coordinate character labels of the actual correction code. -/
def generatedFifthPermutationShort4Character : Fin 56 → Fin 64 :=
  ![
    6, 9, 6, 58, 9, 53, 54, 10, 57, 5, 41, 38, 9, 6,
    5, 10, 5, 10, 9, 6, 9, 6, 0, 41, 0, 12, 5, 9,
    10, 6, 15, 3, 18, 30, 23, 27, 24, 20, 29, 17, 34, 46,
    39, 43, 40, 36, 45, 33, 3, 15, 6, 10, 9, 5, 12, 0
  ]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check only eight actual normalized physical bits per family.
/-- The original physical code intersection has precisely this Walsh label. -/
theorem generatedFifth_permutation_short4_character_bits : ∀ j : Fin 56, ∀ z : Fin 8,
    trialityBinaryBit (generatedFifthPermutationShort4Character j) z =
      golayBooleanCast ((golayEncodedMask 1021).testBit
        (generatedFifthEvenRootCoordinates j z).val) +
      golayBooleanCast ((golayEncodedMask 1021).testBit
        (generatedFifthEvenRootCoordinates j 7).val) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Verify the literal finite signed character rows; no actual-Q expansion is repeated.
/-- Each cached full-phase row is its zero coordinate times its original Walsh character. -/
theorem generatedFifth_permutation_short4_character_row : ∀ j : Fin 56, ∀ e : Fin 64,
    nortonUIntegerSign (generatedFifthPermutationShort4Phase j e) =
      nortonUIntegerSign (generatedFifthPermutationShort4Phase j 0) *
        generatedFifthSignHadamardCache (generatedFifthPermutationShort4Character j) e := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check the genuine original Parker polynomial and correction constants once per family.
/-- The exact original preferred-Q constant equals the zero-sign cached coefficient. -/
theorem generatedFifth_permutation_short4_constant : ∀ j : Fin 56,
    generatedFifthMonomialPermutationModelPhase 4
        (golayLabelCoefficients (generatedFifthEvenRootCode j)) +
      generatedFifthSignFamilyConstant (generatedFifthMonomialPermutationTranslation 4)
        (golayLabelCoefficients (generatedFifthMonomialPermutationModulation 4)) j =
          generatedFifthPermutationShort4Phase j 0 := by
  decide +kernel

/-- The original full actual preferred-Q phase equals the cached binary value. -/
theorem generatedFifth_permutation_short4_actual_phase (j : Fin 56) (e : Fin 64) :
    generatedFifthMonomialPermutationShortPhase 4 (Sum.inr (j, e)) =
      generatedFifthPermutationShort4Phase j e := by
  have hn := generatedFifth_sign_negative_character_of_row
    (⟨1021, by decide⟩ : Fin 2048) j (generatedFifthPermutationShort4Character j)
    (generatedFifthPermutationShort4Phase j)
    (generatedFifth_permutation_short4_character_bits j)
    (generatedFifth_permutation_short4_character_row j) e
  change generatedFifthSignNegativeCharacter (1021 : Fin 4096) j e =
    generatedFifthPermutationShort4Phase j e +
      generatedFifthPermutationShort4Phase j 0 at hn
  rw [generatedFifth_permutation_short_phase_formula, generatedFifth_permutation_short4_constant]
  rw [show generatedFifthMonomialPermutationTranslation 4 = (1021 : Fin 4096) by decide +kernel]
  rw [hn]
  rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
