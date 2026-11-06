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
def generatedFifthSignShortPacket10SourceMasks : Fin 56 → ℕ :=
  ![12297735558912431445, 12297735558912431445, 12273903642954323370, 6531808643310574245,
    17298308641235931120, 18374687574905061120, 14106333703424951235, 14757226376558555955,
    11068046444225730969, 7595767819294840470, 4378557926219170620, 4378557926219170620,
    12297735558912431445, 4378557926219170620, 18374687574905061120, 14757226376558555955,
    7595767819294840470, 6531808643310574245, 17298308641235931120, 14106333703424951235,
    11068046444225730969, 12273903642954323370, 12297735558912431445, 4378557926219170620,
    12273903642954323370, 6531808643310574245, 18374687574905061120, 17298308641235931120,
    6531808643310574245, 12273903642954323370, 17298308641235931120, 18374687574905061120,
    12273903642954323370, 14757226376558555955, 7595767819294840470, 17298308641235931120,
    14757226376558555955, 12273903642954323370, 17298308641235931120, 7595767819294840470,
    14106333703424951235, 6531808643310574245, 18374687574905061120, 11068046444225730969,
    6531808643310574245, 14106333703424951235, 11068046444225730969, 18374687574905061120,
    7595767819294840470, 11068046444225730969, 14106333703424951235, 14757226376558555955,
    11068046444225730969, 7595767819294840470, 14757226376558555955, 14106333703424951235]

/-- Original source Q-code characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket10Source (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket10SourceMasks j).testBit e.val then 1 else 0

/-- Bitmasks of the original correcting Q characters on each actual outgoing family. -/
def generatedFifthSignShortPacket10CorrectionMasks : Fin 56 → ℕ :=
  ![12297735558912431445, 6149008514797120170, 6172840430755228245, 6531808643310574245,
    1148435432473620495, 18374687574905061120, 4340410370284600380, 14757226376558555955,
    7378697629483820646, 7595767819294840470, 4378557926219170620, 14068186147490380995,
    12297735558912431445, 14068186147490380995, 18374687574905061120, 3689517697150995660,
    7595767819294840470, 11914935430398977370, 17298308641235931120, 4340410370284600380,
    11068046444225730969, 6172840430755228245, 12297735558912431445, 14068186147490380995,
    6172840430755228245, 11914935430398977370, 18374687574905061120, 1148435432473620495,
    6531808643310574245, 6172840430755228245, 17298308641235931120, 18374687574905061120,
    6172840430755228245, 3689517697150995660, 7595767819294840470, 1148435432473620495,
    14757226376558555955, 6172840430755228245, 17298308641235931120, 7595767819294840470,
    4340410370284600380, 11914935430398977370, 18374687574905061120, 7378697629483820646,
    6531808643310574245, 4340410370284600380, 11068046444225730969, 18374687574905061120,
    7595767819294840470, 11068046444225730969, 4340410370284600380, 14757226376558555955,
    7378697629483820646, 7595767819294840470, 3689517697150995660, 4340410370284600380]

/-- Original correcting Q characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket10Correction (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket10CorrectionMasks j).testBit e.val then 1 else 0

/-- Sixty-four times the corrected original short coefficient, omitting its common input sign. -/
def generatedFifthSignShortPacket10Numerator (j : Fin 56) (e : Fin 64) : ℤ :=
  (if generatedFifthSignShortPacket10Correction j e = 0 then 1 else -1) *
    ∑ f : Fin 64, generatedFifthSignFourierCache f e *
      (if generatedFifthSignShortPacket10Source j f = 0 then 1 else -1) *
      generatedFifthSignFourierCache (generatedFifthEvenRootSign j) f

/-- Exact character label of the displayed source row. -/
def generatedFifthSignShortPacket10Character : Fin 56 → Fin 64 :=
  ![
    17, 17, 22, 2, 19, 7, 6, 18,
    3, 23, 30, 30, 17, 30, 7, 18,
    23, 2, 19, 6, 3, 22, 17, 30,
    22, 2, 7, 19, 2, 22, 19, 7,
    22, 18, 23, 19, 18, 22, 19, 23,
    6, 2, 7, 3, 2, 6, 3, 7,
    23, 3, 6, 18, 3, 23, 18, 6]

/-- The common sign of a source character row. -/
def generatedFifthSignShortPacket10Alpha (j : Fin 56) : ℤ :=
  if generatedFifthSignShortPacket10Source j 0 = 0 then 1 else -1

/-- The common sign is a unit of square one. -/
theorem generatedFifthSignShortPacket10_alpha_sq (j : Fin 56) :
    generatedFifthSignShortPacket10Alpha j * generatedFifthSignShortPacket10Alpha j = 1 := by
  unfold generatedFifthSignShortPacket10Alpha
  split <;> norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the displayed characters, with no Fourier sum to normalize.
/-- Each displayed source row is its stated genuine Walsh character. -/
theorem generatedFifthSignShortPacket10_source_character :
    ∀ j : Fin 56, ∀ f : Fin 64,
    (if generatedFifthSignShortPacket10Source j f = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket10Alpha j *
        generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket10Character j) f := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the correcting character against the genuine quadratic diagonal.
/-- Each correcting row is the exact Fourier-conjugate character. -/
theorem generatedFifthSignShortPacket10_correction_character :
    ∀ j : Fin 56, ∀ e : Fin 64,
    (if generatedFifthSignShortPacket10Correction j e = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket10Alpha j *
        (trialityIntegerDiagonal (generatedFifthEvenRootSign j) *
          trialityIntegerDiagonal
            (trialityXor (generatedFifthSignShortPacket10Character j)
              (generatedFifthEvenRootSign j)) *
          generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket10Character j) e) := by
  decide +kernel

/-- Exact character transport restores every original supported octad coefficient. -/
theorem generatedFifthSignShortPacket10_numerator (j : Fin 56) (e : Fin 64) :
    generatedFifthSignShortPacket10Numerator j e =
      8 * generatedFifthSignFourierCache e (generatedFifthEvenRootSign j) := by
  unfold generatedFifthSignShortPacket10Numerator
  simp_rw [generatedFifthSignShortPacket10_correction_character,
    generatedFifthSignShortPacket10_source_character,
    generatedFifth_sign_hadamard_cache, generatedFifth_sign_fourier_cache]
  exact generatedFifth_sign_fourier_character_signed _ (generatedFifthSignShortPacket10_alpha_sq j)
    (generatedFifthSignShortPacket10Character j) (generatedFifthEvenRootSign j) e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
