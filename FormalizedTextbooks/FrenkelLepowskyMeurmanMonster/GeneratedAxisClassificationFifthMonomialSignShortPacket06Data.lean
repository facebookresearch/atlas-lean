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
def generatedFifthSignShortPacket06SourceMasks : Fin 56 → ℕ :=
  ![4294967295, 17298308641235931120, 71777214294589695, 71777214294589695,
    71777214294589695, 71777214294589695, 7595767820052752745, 7595767820052752745,
    7595767820052752745, 7595767820052752745, 10838310072981296745, 0,
    17298308641235931120, 7608433999976240745, 281470681808895, 11067990150089369190,
    7608433999976240745, 17298062221247451120, 17298308641235931120, 7608384715978544745,
    11068046443366737510, 4294967295, 11936045732788001370, 10838310072981296745,
    4294967295, 4294967295, 18374687574905061120, 71777214294589695,
    18374687574905061120, 71777214294589695, 4294967295, 4294967295,
    0, 10838310072981296745, 71777214294589695, 71777214294589695,
    71777214294589695, 71777214294589695, 0, 10838310072981296745,
    7608384715226507670, 18446462598732906495, 18374687574905061120, 18374687574905061120,
    18374687574905061120, 18374687574905061120, 7608384715226507670, 18446462598732906495,
    7608433999976240745, 7608433999976240745, 10851025925711500950, 7595767820052752745,
    10851025925711500950, 7595767820052752745, 7608433999976240745, 7608433999976240745]

/-- Original source Q-code characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket06Source (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket06SourceMasks j).testBit e.val then 1 else 0

/-- Bitmasks of the original correcting Q characters on each actual outgoing family. -/
def generatedFifthSignShortPacket06CorrectionMasks : Fin 56 → ℕ :=
  ![18446744069414584320, 17298308641235931120, 18374966859414961920, 71777214294589695,
    71777214294589695, 18374966859414961920, 7595767820052752745, 10850976253656798870,
    10850976253656798870, 7595767820052752745, 7608434000728254870, 0,
    1148435432473620495, 7608433999976240745, 18446462603027742720, 11067990150089369190,
    7608433999976240745, 1148681852462100495, 17298308641235931120, 10838359357731006870,
    7378697630342814105, 4294967295, 6510698340921550245, 10838310072981296745,
    18446744069414584320, 4294967295, 18374687574905061120, 71777214294589695,
    72056498804490495, 18374966859414961920, 18446744069414584320, 4294967295,
    0, 7608434000728254870, 18374966859414961920, 18374966859414961920,
    71777214294589695, 71777214294589695, 0, 7608434000728254870,
    10838359358483043945, 18446462598732906495, 18374687574905061120, 18374687574905061120,
    72056498804490495, 72056498804490495, 10838359358483043945, 18446462598732906495,
    10838310073733310870, 7608433999976240745, 10851025925711500950, 7595767820052752745,
    7595718147998050665, 10850976253656798870, 10838310073733310870, 7608433999976240745]

/-- Original correcting Q characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket06Correction (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket06CorrectionMasks j).testBit e.val then 1 else 0

/-- Sixty-four times the corrected original short coefficient, omitting its common input sign. -/
def generatedFifthSignShortPacket06Numerator (j : Fin 56) (e : Fin 64) : ℤ :=
  (if generatedFifthSignShortPacket06Correction j e = 0 then 1 else -1) *
    ∑ f : Fin 64, generatedFifthSignFourierCache f e *
      (if generatedFifthSignShortPacket06Source j f = 0 then 1 else -1) *
      generatedFifthSignFourierCache (generatedFifthEvenRootSign j) f

/-- Exact character label of the displayed source row. -/
def generatedFifthSignShortPacket06Character : Fin 56 → Fin 64 :=
  ![
    31, 19, 55, 55, 55, 55, 8, 8,
    8, 8, 63, 0, 19, 32, 47, 44,
    32, 35, 19, 16, 28, 31, 42, 63,
    31, 31, 7, 55, 7, 55, 31, 31,
    0, 63, 55, 55, 55, 55, 0, 63,
    15, 48, 7, 7, 7, 7, 15, 48,
    32, 32, 56, 8, 56, 8, 32, 32]

/-- The common sign of a source character row. -/
def generatedFifthSignShortPacket06Alpha (j : Fin 56) : ℤ :=
  if generatedFifthSignShortPacket06Source j 0 = 0 then 1 else -1

/-- The common sign is a unit of square one. -/
theorem generatedFifthSignShortPacket06_alpha_sq (j : Fin 56) :
    generatedFifthSignShortPacket06Alpha j * generatedFifthSignShortPacket06Alpha j = 1 := by
  unfold generatedFifthSignShortPacket06Alpha
  split <;> norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the displayed characters, with no Fourier sum to normalize.
/-- Each displayed source row is its stated genuine Walsh character. -/
theorem generatedFifthSignShortPacket06_source_character :
    ∀ j : Fin 56, ∀ f : Fin 64,
    (if generatedFifthSignShortPacket06Source j f = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket06Alpha j *
        generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket06Character j) f := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the correcting character against the genuine quadratic diagonal.
/-- Each correcting row is the exact Fourier-conjugate character. -/
theorem generatedFifthSignShortPacket06_correction_character :
    ∀ j : Fin 56, ∀ e : Fin 64,
    (if generatedFifthSignShortPacket06Correction j e = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket06Alpha j *
        (trialityIntegerDiagonal (generatedFifthEvenRootSign j) *
          trialityIntegerDiagonal
            (trialityXor (generatedFifthSignShortPacket06Character j)
              (generatedFifthEvenRootSign j)) *
          generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket06Character j) e) := by
  decide +kernel

/-- Exact character transport restores every original supported octad coefficient. -/
theorem generatedFifthSignShortPacket06_numerator (j : Fin 56) (e : Fin 64) :
    generatedFifthSignShortPacket06Numerator j e =
      8 * generatedFifthSignFourierCache e (generatedFifthEvenRootSign j) := by
  unfold generatedFifthSignShortPacket06Numerator
  simp_rw [generatedFifthSignShortPacket06_correction_character,
    generatedFifthSignShortPacket06_source_character,
    generatedFifth_sign_hadamard_cache, generatedFifth_sign_fourier_cache]
  exact generatedFifth_sign_fourier_character_signed _ (generatedFifthSignShortPacket06_alpha_sq j)
    (generatedFifthSignShortPacket06Character j) (generatedFifthEvenRootSign j) e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
