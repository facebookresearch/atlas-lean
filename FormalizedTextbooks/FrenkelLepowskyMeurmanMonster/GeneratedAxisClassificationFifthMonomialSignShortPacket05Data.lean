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
def generatedFifthSignShortPacket05SourceMasks : Fin 56 → ℕ :=
  ![14714328927833961420, 4294967295, 4294967295, 281470681808895,
    4294967295, 281470681808895, 7608384715978544745, 7608433999976240745,
    7608384715978544745, 7608433999976240745, 0, 4294967295,
    14714328927833961420, 4294967295, 18374687579166474495, 7595767819294840470,
    7595767819294840470, 18374687579166474495, 18374966855153418495, 7595718148755986070,
    7595718148755986070, 18374966855153418495, 14714328927833961420, 4294967295,
    18374966855153418495, 17361641477348724495, 18446462598732906495, 0,
    18446462598732906495, 0, 17361641477348724495, 18374966855153418495,
    18374966855153418495, 7393108928392436070, 4294967295, 4294967295,
    4294967295, 4294967295, 17361641477348724495, 7595767819294840470,
    7595767819294840470, 17361641477348724495, 4294967295, 4294967295,
    4294967295, 4294967295, 7393108928392436070, 18374966855153418495,
    7595767819294840470, 7393108928392436070, 7608384715226507670, 10838310072981296745,
    7608384715226507670, 10838310072981296745, 7393108928392436070, 7595767819294840470]

/-- Original source Q-code characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket05Source (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket05SourceMasks j).testBit e.val then 1 else 0

/-- Bitmasks of the original correcting Q characters on each actual outgoing family. -/
def generatedFifthSignShortPacket05CorrectionMasks : Fin 56 → ℕ :=
  ![3732415145875590195, 4294967295, 4294967295, 18446462603027742720,
    4294967295, 18446462603027742720, 10838359357731006870, 7608433999976240745,
    10838359357731006870, 7608433999976240745, 0, 18446744069414584320,
    3732415145875590195, 4294967295, 18374687579166474495, 10850976254414711145,
    7595767819294840470, 72056494543077120, 71777218556133120, 7595718148755986070,
    10851025924953565545, 18374966855153418495, 14714328927833961420, 18446744069414584320,
    18374966855153418495, 1085102596360827120, 18446462598732906495, 0,
    18446462598732906495, 0, 1085102596360827120, 18374966855153418495,
    18374966855153418495, 11053635145317115545, 4294967295, 4294967295,
    4294967295, 4294967295, 1085102596360827120, 7595767819294840470,
    10850976254414711145, 17361641477348724495, 18446744069414584320, 18446744069414584320,
    18446744069414584320, 18446744069414584320, 7393108928392436070, 71777218556133120,
    7595767819294840470, 11053635145317115545, 7608384715226507670, 10838310072981296745,
    7608384715226507670, 10838310072981296745, 11053635145317115545, 7595767819294840470]

/-- Original correcting Q characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket05Correction (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket05CorrectionMasks j).testBit e.val then 1 else 0

/-- Sixty-four times the corrected original short coefficient, omitting its common input sign. -/
def generatedFifthSignShortPacket05Numerator (j : Fin 56) (e : Fin 64) : ℤ :=
  (if generatedFifthSignShortPacket05Correction j e = 0 then 1 else -1) *
    ∑ f : Fin 64, generatedFifthSignFourierCache f e *
      (if generatedFifthSignShortPacket05Source j f = 0 then 1 else -1) *
      generatedFifthSignFourierCache (generatedFifthEvenRootSign j) f

/-- Exact character label of the displayed source row. -/
def generatedFifthSignShortPacket05Character : Fin 56 → Fin 64 :=
  ![
    21, 31, 31, 47, 31, 47, 16, 32,
    16, 32, 0, 31, 21, 31, 24, 23,
    23, 24, 40, 39, 39, 40, 21, 31,
    40, 36, 48, 0, 48, 0, 36, 40,
    40, 27, 31, 31, 31, 31, 36, 23,
    23, 36, 31, 31, 31, 31, 27, 40,
    23, 27, 15, 63, 15, 63, 27, 23]

/-- The common sign of a source character row. -/
def generatedFifthSignShortPacket05Alpha (j : Fin 56) : ℤ :=
  if generatedFifthSignShortPacket05Source j 0 = 0 then 1 else -1

/-- The common sign is a unit of square one. -/
theorem generatedFifthSignShortPacket05_alpha_sq (j : Fin 56) :
    generatedFifthSignShortPacket05Alpha j * generatedFifthSignShortPacket05Alpha j = 1 := by
  unfold generatedFifthSignShortPacket05Alpha
  split <;> norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the displayed characters, with no Fourier sum to normalize.
/-- Each displayed source row is its stated genuine Walsh character. -/
theorem generatedFifthSignShortPacket05_source_character :
    ∀ j : Fin 56, ∀ f : Fin 64,
    (if generatedFifthSignShortPacket05Source j f = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket05Alpha j *
        generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket05Character j) f := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the correcting character against the genuine quadratic diagonal.
/-- Each correcting row is the exact Fourier-conjugate character. -/
theorem generatedFifthSignShortPacket05_correction_character :
    ∀ j : Fin 56, ∀ e : Fin 64,
    (if generatedFifthSignShortPacket05Correction j e = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket05Alpha j *
        (trialityIntegerDiagonal (generatedFifthEvenRootSign j) *
          trialityIntegerDiagonal
            (trialityXor (generatedFifthSignShortPacket05Character j)
              (generatedFifthEvenRootSign j)) *
          generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket05Character j) e) := by
  decide +kernel

/-- Exact character transport restores every original supported octad coefficient. -/
theorem generatedFifthSignShortPacket05_numerator (j : Fin 56) (e : Fin 64) :
    generatedFifthSignShortPacket05Numerator j e =
      8 * generatedFifthSignFourierCache e (generatedFifthEvenRootSign j) := by
  unfold generatedFifthSignShortPacket05Numerator
  simp_rw [generatedFifthSignShortPacket05_correction_character,
    generatedFifthSignShortPacket05_source_character,
    generatedFifth_sign_hadamard_cache, generatedFifth_sign_fourier_cache]
  exact generatedFifth_sign_fourier_character_signed _ (generatedFifthSignShortPacket05_alpha_sq j)
    (generatedFifthSignShortPacket05Character j) (generatedFifthEvenRootSign j) e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
