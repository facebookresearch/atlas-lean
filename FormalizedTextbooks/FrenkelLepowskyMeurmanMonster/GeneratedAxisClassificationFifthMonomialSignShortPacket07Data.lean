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
def generatedFifthSignShortPacket07SourceMasks : Fin 56 → ℕ :=
  ![7608433999976240745, 11936045732788001370, 0, 17298308644996116495,
    17298308644996116495, 0, 10838310072981296745, 7378753924479149670,
    7378753924479149670, 10838310072981296745, 4294967295, 0,
    11936045732788001370, 10838310072981296745, 18374687574905061120, 71777214294589695,
    71777214294589695, 18374687574905061120, 71777214294589695, 18374687574905061120,
    18374687574905061120, 71777214294589695, 6172933524171347370, 4294967295,
    4294967295, 281470681808895, 281470681808895, 17298308641235931120,
    17298062221247451120, 4294967295, 4294967295, 281470681808895,
    4294967295, 7608433999976240745, 7608433999976240745, 17298308641235931120,
    11067990150089369190, 4294967295, 4294967295, 7608433999976240745,
    7608433999976240745, 4294967295, 4294967295, 11067990150089369190,
    17298308641235931120, 7608433999976240745, 7608433999976240745, 4294967295,
    4294967295, 281470681808895, 281470681808895, 17298308641235931120,
    17298062221247451120, 4294967295, 4294967295, 281470681808895]

/-- Original source Q-code characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket07Source (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket07SourceMasks j).testBit e.val then 1 else 0

/-- Bitmasks of the original correcting Q characters on each actual outgoing family. -/
def generatedFifthSignShortPacket07CorrectionMasks : Fin 56 → ℕ :=
  ![10838310073733310870, 11936045732788001370, 0, 1148435428713435120,
    1148435428713435120, 0, 7608434000728254870, 7378753924479149670,
    7378753924479149670, 7608434000728254870, 18446744069414584320, 0,
    11936045732788001370, 7608434000728254870, 18374687574905061120, 18374966859414961920,
    71777214294589695, 72056498804490495, 71777214294589695, 72056498804490495,
    18374687574905061120, 18374966859414961920, 6172933524171347370, 18446744069414584320,
    18446744069414584320, 281470681808895, 18446462603027742720, 1148435432473620495,
    17298062221247451120, 4294967295, 18446744069414584320, 281470681808895,
    18446744069414584320, 7608433999976240745, 10838310073733310870, 1148435432473620495,
    11067990150089369190, 4294967295, 18446744069414584320, 7608433999976240745,
    10838310073733310870, 4294967295, 18446744069414584320, 7378753923620182425,
    17298308641235931120, 7608433999976240745, 10838310073733310870, 4294967295,
    4294967295, 18446462603027742720, 281470681808895, 17298308641235931120,
    1148681852462100495, 18446744069414584320, 4294967295, 18446462603027742720]

/-- Original correcting Q characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket07Correction (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket07CorrectionMasks j).testBit e.val then 1 else 0

/-- Sixty-four times the corrected original short coefficient, omitting its common input sign. -/
def generatedFifthSignShortPacket07Numerator (j : Fin 56) (e : Fin 64) : ℤ :=
  (if generatedFifthSignShortPacket07Correction j e = 0 then 1 else -1) *
    ∑ f : Fin 64, generatedFifthSignFourierCache f e *
      (if generatedFifthSignShortPacket07Source j f = 0 then 1 else -1) *
      generatedFifthSignFourierCache (generatedFifthEvenRootSign j) f

/-- Exact character label of the displayed source row. -/
def generatedFifthSignShortPacket07Character : Fin 56 → Fin 64 :=
  ![
    32, 42, 0, 12, 12, 0, 63, 51,
    51, 63, 31, 0, 42, 63, 7, 55,
    55, 7, 55, 7, 7, 55, 57, 31,
    31, 47, 47, 19, 35, 31, 31, 47,
    31, 32, 32, 19, 44, 31, 31, 32,
    32, 31, 31, 44, 19, 32, 32, 31,
    31, 47, 47, 19, 35, 31, 31, 47]

/-- The common sign of a source character row. -/
def generatedFifthSignShortPacket07Alpha (j : Fin 56) : ℤ :=
  if generatedFifthSignShortPacket07Source j 0 = 0 then 1 else -1

/-- The common sign is a unit of square one. -/
theorem generatedFifthSignShortPacket07_alpha_sq (j : Fin 56) :
    generatedFifthSignShortPacket07Alpha j * generatedFifthSignShortPacket07Alpha j = 1 := by
  unfold generatedFifthSignShortPacket07Alpha
  split <;> norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the displayed characters, with no Fourier sum to normalize.
/-- Each displayed source row is its stated genuine Walsh character. -/
theorem generatedFifthSignShortPacket07_source_character :
    ∀ j : Fin 56, ∀ f : Fin 64,
    (if generatedFifthSignShortPacket07Source j f = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket07Alpha j *
        generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket07Character j) f := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the correcting character against the genuine quadratic diagonal.
/-- Each correcting row is the exact Fourier-conjugate character. -/
theorem generatedFifthSignShortPacket07_correction_character :
    ∀ j : Fin 56, ∀ e : Fin 64,
    (if generatedFifthSignShortPacket07Correction j e = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket07Alpha j *
        (trialityIntegerDiagonal (generatedFifthEvenRootSign j) *
          trialityIntegerDiagonal
            (trialityXor (generatedFifthSignShortPacket07Character j)
              (generatedFifthEvenRootSign j)) *
          generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket07Character j) e) := by
  decide +kernel

/-- Exact character transport restores every original supported octad coefficient. -/
theorem generatedFifthSignShortPacket07_numerator (j : Fin 56) (e : Fin 64) :
    generatedFifthSignShortPacket07Numerator j e =
      8 * generatedFifthSignFourierCache e (generatedFifthEvenRootSign j) := by
  unfold generatedFifthSignShortPacket07Numerator
  simp_rw [generatedFifthSignShortPacket07_correction_character,
    generatedFifthSignShortPacket07_source_character,
    generatedFifth_sign_hadamard_cache, generatedFifth_sign_fourier_cache]
  exact generatedFifth_sign_fourier_character_signed _ (generatedFifthSignShortPacket07_alpha_sq j)
    (generatedFifthSignShortPacket07Character j) (generatedFifthEvenRootSign j) e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
