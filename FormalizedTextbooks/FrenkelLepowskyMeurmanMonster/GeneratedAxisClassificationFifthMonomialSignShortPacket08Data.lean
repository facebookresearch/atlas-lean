/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignFourierCharacter

/-! A bounded integer short-coordinate packet for one original corrected Golay sign word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/-- Bitmasks of the original source Q-code characters on each actual outgoing family. -/
def generatedFifthSignShortPacket08SourceMasks : Fin 56 → ℕ :=
  ![7608433999976240745, 7608433999976240745, 0, 0,
    11068046444225730969, 11068046444225730969, 10838310072981296745, 10838310072981296745,
    1148681856222171120, 1148681856222171120, 17298308644996116495, 17298308644996116495,
    11067990150089369190, 17298308641235931120, 7378753924479149670, 7378753924479149670,
    1148681856222171120, 1148681856222171120, 7608384715226507670, 7608384715226507670,
    0, 0, 14106333701151145020, 7378753924479149670,
    14757395256390660915, 14757226376558555955, 14757226376558555955, 14757395256390660915,
    14757226376558555955, 14757395256390660915, 14757395256390660915, 14757226376558555955,
    3689348814741910323, 6531808643310574245, 6531808643310574245, 3689348814741910323,
    6531808643310574245, 3689348814741910323, 3689348814741910323, 6531808643310574245,
    11915017572901889370, 14757226373981654220, 14757226373981654220, 11915017572901889370,
    14757226373981654220, 11915017572901889370, 11915017572901889370, 14757226373981654220,
    6531808642057217370, 6531726502061057370, 6531726502061057370, 6531808642057217370,
    6531726502061057370, 6531808642057217370, 6531808642057217370, 6531726502061057370]

/-- Original source Q-code characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket08Source (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket08SourceMasks j).testBit e.val then 1 else 0

/-- Bitmasks of the original correcting Q characters on each actual outgoing family. -/
def generatedFifthSignShortPacket08CorrectionMasks : Fin 56 → ℕ :=
  ![10838310073733310870, 10838310073733310870, 0, 0,
    7378697629483820646, 7378697629483820646, 7608434000728254870, 7608434000728254870,
    1148681856222171120, 1148681856222171120, 1148435428713435120, 1148435428713435120,
    11067990150089369190, 17298308641235931120, 7378753924479149670, 7378753924479149670,
    1148681856222171120, 1148681856222171120, 7608384715226507670, 7608384715226507670,
    0, 0, 14106333701151145020, 7378753924479149670,
    3689348817318890700, 14757226376558555955, 3689517697150995660, 14757395256390660915,
    14757226376558555955, 3689348817318890700, 14757395256390660915, 3689517697150995660,
    14757395258967641292, 6531808643310574245, 11914935430398977370, 3689348814741910323,
    6531808643310574245, 14757395258967641292, 3689348814741910323, 11914935430398977370,
    6531726500807662245, 14757226373981654220, 3689517699727897395, 11915017572901889370,
    14757226373981654220, 6531726500807662245, 11915017572901889370, 3689517699727897395,
    11914935431652334245, 6531726502061057370, 11915017571648494245, 6531808642057217370,
    6531726502061057370, 11914935431652334245, 6531808642057217370, 11915017571648494245]

/-- Original correcting Q characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket08Correction (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket08CorrectionMasks j).testBit e.val then 1 else 0

/-- Sixty-four times the corrected original short coefficient, omitting its common input sign. -/
def generatedFifthSignShortPacket08Numerator (j : Fin 56) (e : Fin 64) : ℤ :=
  (if generatedFifthSignShortPacket08Correction j e = 0 then 1 else -1) *
    ∑ f : Fin 64, generatedFifthSignFourierCache f e *
      (if generatedFifthSignShortPacket08Source j f = 0 then 1 else -1) *
      generatedFifthSignFourierCache (generatedFifthEvenRootSign j) f

/-- Exact character label of the displayed source row. -/
def generatedFifthSignShortPacket08Character : Fin 56 → Fin 64 :=
  ![
    32, 32, 0, 0, 3, 3, 63, 63,
    60, 60, 12, 12, 44, 19, 51, 51,
    60, 60, 15, 15, 0, 0, 25, 51,
    34, 18, 18, 34, 18, 34, 34, 18,
    61, 2, 2, 61, 2, 61, 61, 2,
    50, 13, 13, 50, 13, 50, 50, 13,
    29, 45, 45, 29, 45, 29, 29, 45]

/-- The common sign of a source character row. -/
def generatedFifthSignShortPacket08Alpha (j : Fin 56) : ℤ :=
  if generatedFifthSignShortPacket08Source j 0 = 0 then 1 else -1

/-- The common sign is a unit of square one. -/
theorem generatedFifthSignShortPacket08_alpha_sq (j : Fin 56) :
    generatedFifthSignShortPacket08Alpha j * generatedFifthSignShortPacket08Alpha j = 1 := by
  unfold generatedFifthSignShortPacket08Alpha
  split <;> norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the displayed characters, with no Fourier sum to normalize.
/-- Each displayed source row is its stated genuine Walsh character. -/
theorem generatedFifthSignShortPacket08_source_character :
    ∀ j : Fin 56, ∀ f : Fin 64,
    (if generatedFifthSignShortPacket08Source j f = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket08Alpha j *
        generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket08Character j) f := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the correcting character against the genuine quadratic diagonal.
/-- Each correcting row is the exact Fourier-conjugate character. -/
theorem generatedFifthSignShortPacket08_correction_character :
    ∀ j : Fin 56, ∀ e : Fin 64,
    (if generatedFifthSignShortPacket08Correction j e = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket08Alpha j *
        (trialityIntegerDiagonal (generatedFifthEvenRootSign j) *
          trialityIntegerDiagonal
            (trialityXor (generatedFifthSignShortPacket08Character j)
              (generatedFifthEvenRootSign j)) *
          generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket08Character j) e) := by
  decide +kernel

/-- Exact character transport restores every original supported octad coefficient. -/
theorem generatedFifthSignShortPacket08_numerator (j : Fin 56) (e : Fin 64) :
    generatedFifthSignShortPacket08Numerator j e =
      8 * generatedFifthSignFourierCache e (generatedFifthEvenRootSign j) := by
  unfold generatedFifthSignShortPacket08Numerator
  simp_rw [generatedFifthSignShortPacket08_correction_character,
    generatedFifthSignShortPacket08_source_character,
    generatedFifth_sign_hadamard_cache, generatedFifth_sign_fourier_cache]
  exact generatedFifth_sign_fourier_character_signed _ (generatedFifthSignShortPacket08_alpha_sq j)
    (generatedFifthSignShortPacket08Character j) (generatedFifthEvenRootSign j) e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
