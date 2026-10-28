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
def generatedFifthSignShortPacket04SourceMasks : Fin 56 → ℕ :=
  ![7378753924479149670, 10838310072981296745, 4294967295, 4294967295,
    4294967295, 4294967295, 4294967295, 4294967295,
    4294967295, 4294967295, 0, 10838310072981296745,
    7378753924479149670, 10838310072981296745, 4294967295, 17298308641235931120,
    4294967295, 17298308641235931120, 17298308641235931120, 4294967295,
    17298308641235931120, 4294967295, 7378753924479149670, 10838310072981296745,
    71777214294589695, 18374687574905061120, 4294967295, 4294967295,
    4294967295, 4294967295, 71777214294589695, 18374687574905061120,
    71777214294589695, 71777214294589695, 10838310072981296745, 0,
    10838310072981296745, 0, 71777214294589695, 71777214294589695,
    18374687574905061120, 18374687574905061120, 18446462598732906495, 7608384715226507670,
    18446462598732906495, 7608384715226507670, 18374687574905061120, 18374687574905061120,
    71777214294589695, 18374687574905061120, 4294967295, 4294967295,
    4294967295, 4294967295, 71777214294589695, 18374687574905061120]

/-- Original source Q-code characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket04Source (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket04SourceMasks j).testBit e.val then 1 else 0

/-- Bitmasks of the original correcting Q characters on each actual outgoing family. -/
def generatedFifthSignShortPacket04CorrectionMasks : Fin 56 → ℕ :=
  ![11067990149230401945, 10838310072981296745, 4294967295, 18446744069414584320,
    4294967295, 18446744069414584320, 18446744069414584320, 4294967295,
    18446744069414584320, 4294967295, 0, 7608434000728254870,
    7378753924479149670, 7608434000728254870, 4294967295, 1148435432473620495,
    18446744069414584320, 17298308641235931120, 17298308641235931120, 18446744069414584320,
    1148435432473620495, 4294967295, 11067990149230401945, 10838310072981296745,
    71777214294589695, 72056498804490495, 4294967295, 4294967295,
    4294967295, 4294967295, 18374966859414961920, 18374687574905061120,
    71777214294589695, 18374966859414961920, 10838310072981296745, 0,
    10838310072981296745, 0, 18374966859414961920, 71777214294589695,
    18374687574905061120, 72056498804490495, 18446462598732906495, 7608384715226507670,
    18446462598732906495, 7608384715226507670, 72056498804490495, 18374687574905061120,
    18374966859414961920, 18374687574905061120, 18446744069414584320, 18446744069414584320,
    18446744069414584320, 18446744069414584320, 71777214294589695, 72056498804490495]

/-- Original correcting Q characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket04Correction (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket04CorrectionMasks j).testBit e.val then 1 else 0

/-- Sixty-four times the corrected original short coefficient, omitting its common input sign. -/
def generatedFifthSignShortPacket04Numerator (j : Fin 56) (e : Fin 64) : ℤ :=
  (if generatedFifthSignShortPacket04Correction j e = 0 then 1 else -1) *
    ∑ f : Fin 64, generatedFifthSignFourierCache f e *
      (if generatedFifthSignShortPacket04Source j f = 0 then 1 else -1) *
      generatedFifthSignFourierCache (generatedFifthEvenRootSign j) f

/-- Exact character label of the displayed source row. -/
def generatedFifthSignShortPacket04Character : Fin 56 → Fin 64 :=
  ![
    51, 63, 31, 31, 31, 31, 31, 31,
    31, 31, 0, 63, 51, 63, 31, 19,
    31, 19, 19, 31, 19, 31, 51, 63,
    55, 7, 31, 31, 31, 31, 55, 7,
    55, 55, 63, 0, 63, 0, 55, 55,
    7, 7, 48, 15, 48, 15, 7, 7,
    55, 7, 31, 31, 31, 31, 55, 7]

/-- The common sign of a source character row. -/
def generatedFifthSignShortPacket04Alpha (j : Fin 56) : ℤ :=
  if generatedFifthSignShortPacket04Source j 0 = 0 then 1 else -1

/-- The common sign is a unit of square one. -/
theorem generatedFifthSignShortPacket04_alpha_sq (j : Fin 56) :
    generatedFifthSignShortPacket04Alpha j * generatedFifthSignShortPacket04Alpha j = 1 := by
  unfold generatedFifthSignShortPacket04Alpha
  split <;> norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the displayed characters, with no Fourier sum to normalize.
/-- Each displayed source row is its stated genuine Walsh character. -/
theorem generatedFifthSignShortPacket04_source_character :
    ∀ j : Fin 56, ∀ f : Fin 64,
    (if generatedFifthSignShortPacket04Source j f = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket04Alpha j *
        generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket04Character j) f := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the correcting character against the genuine quadratic diagonal.
/-- Each correcting row is the exact Fourier-conjugate character. -/
theorem generatedFifthSignShortPacket04_correction_character :
    ∀ j : Fin 56, ∀ e : Fin 64,
    (if generatedFifthSignShortPacket04Correction j e = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket04Alpha j *
        (trialityIntegerDiagonal (generatedFifthEvenRootSign j) *
          trialityIntegerDiagonal
            (trialityXor (generatedFifthSignShortPacket04Character j)
              (generatedFifthEvenRootSign j)) *
          generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket04Character j) e) := by
  decide +kernel

/-- Exact character transport restores every original supported octad coefficient. -/
theorem generatedFifthSignShortPacket04_numerator (j : Fin 56) (e : Fin 64) :
    generatedFifthSignShortPacket04Numerator j e =
      8 * generatedFifthSignFourierCache e (generatedFifthEvenRootSign j) := by
  unfold generatedFifthSignShortPacket04Numerator
  simp_rw [generatedFifthSignShortPacket04_correction_character,
    generatedFifthSignShortPacket04_source_character,
    generatedFifth_sign_hadamard_cache, generatedFifth_sign_fourier_cache]
  exact generatedFifth_sign_fourier_character_signed _ (generatedFifthSignShortPacket04_alpha_sq j)
    (generatedFifthSignShortPacket04Character j) (generatedFifthEvenRootSign j) e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
