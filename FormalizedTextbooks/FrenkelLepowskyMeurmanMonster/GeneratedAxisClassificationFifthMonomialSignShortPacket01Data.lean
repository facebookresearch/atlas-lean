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
def generatedFifthSignShortPacket01SourceMasks : Fin 56 → ℕ :=
  ![0, 0, 11068046444225730969, 11068046444225730969,
    11068046444225730969, 11068046444225730969, 11068046444225730969, 11068046444225730969,
    11068046444225730969, 11068046444225730969, 7608384715226507670, 7608384715226507670,
    7608384715226507670, 7608384715226507670, 7608384715226507670, 7608384715226507670,
    7608384715226507670, 7608384715226507670, 7608384715226507670, 7608384715226507670,
    7608384715226507670, 7608384715226507670, 0, 0,
    11068046444225730969, 11068046444225730969, 11068046444225730969, 11068046444225730969,
    11068046444225730969, 11068046444225730969, 11068046444225730969, 11068046444225730969,
    7378753924479149670, 7378753924479149670, 7378753924479149670, 7378753924479149670,
    7378753924479149670, 7378753924479149670, 7378753924479149670, 7378753924479149670,
    7378753924479149670, 7378753924479149670, 7378753924479149670, 7378753924479149670,
    7378753924479149670, 7378753924479149670, 7378753924479149670, 7378753924479149670,
    11068046444225730969, 11068046444225730969, 11068046444225730969, 11068046444225730969,
    11068046444225730969, 11068046444225730969, 11068046444225730969, 11068046444225730969]

/-- Original source Q-code characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket01Source (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket01SourceMasks j).testBit e.val then 1 else 0

/-- Bitmasks of the original correcting Q characters on each actual outgoing family. -/
def generatedFifthSignShortPacket01CorrectionMasks : Fin 56 → ℕ :=
  ![0, 0, 11068046444225730969, 11068046444225730969,
    7378697629483820646, 7378697629483820646, 11068046444225730969, 11068046444225730969,
    7378697629483820646, 7378697629483820646, 10838359358483043945, 10838359358483043945,
    10838359358483043945, 10838359358483043945, 10838359358483043945, 10838359358483043945,
    10838359358483043945, 10838359358483043945, 7608384715226507670, 7608384715226507670,
    7608384715226507670, 7608384715226507670, 0, 0,
    7378697629483820646, 7378697629483820646, 7378697629483820646, 7378697629483820646,
    11068046444225730969, 11068046444225730969, 11068046444225730969, 11068046444225730969,
    7378753924479149670, 7378753924479149670, 7378753924479149670, 7378753924479149670,
    11067990149230401945, 11067990149230401945, 11067990149230401945, 11067990149230401945,
    11067990149230401945, 11067990149230401945, 11067990149230401945, 11067990149230401945,
    7378753924479149670, 7378753924479149670, 7378753924479149670, 7378753924479149670,
    11068046444225730969, 11068046444225730969, 11068046444225730969, 11068046444225730969,
    7378697629483820646, 7378697629483820646, 7378697629483820646, 7378697629483820646]

/-- Original correcting Q characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket01Correction (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket01CorrectionMasks j).testBit e.val then 1 else 0

/-- Sixty-four times the corrected original short coefficient, omitting its common input sign. -/
def generatedFifthSignShortPacket01Numerator (j : Fin 56) (e : Fin 64) : ℤ :=
  (if generatedFifthSignShortPacket01Correction j e = 0 then 1 else -1) *
    ∑ f : Fin 64, generatedFifthSignFourierCache f e *
      (if generatedFifthSignShortPacket01Source j f = 0 then 1 else -1) *
      generatedFifthSignFourierCache (generatedFifthEvenRootSign j) f

/-- Exact character label of the displayed source row. -/
def generatedFifthSignShortPacket01Character : Fin 56 → Fin 64 :=
  ![
    0, 0, 3, 3, 3, 3, 3, 3,
    3, 3, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 0, 0,
    3, 3, 3, 3, 3, 3, 3, 3,
    51, 51, 51, 51, 51, 51, 51, 51,
    51, 51, 51, 51, 51, 51, 51, 51,
    3, 3, 3, 3, 3, 3, 3, 3]

/-- The common sign of a source character row. -/
def generatedFifthSignShortPacket01Alpha (j : Fin 56) : ℤ :=
  if generatedFifthSignShortPacket01Source j 0 = 0 then 1 else -1

/-- The common sign is a unit of square one. -/
theorem generatedFifthSignShortPacket01_alpha_sq (j : Fin 56) :
    generatedFifthSignShortPacket01Alpha j * generatedFifthSignShortPacket01Alpha j = 1 := by
  unfold generatedFifthSignShortPacket01Alpha
  split <;> norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the displayed characters, with no Fourier sum to normalize.
/-- Each displayed source row is its stated genuine Walsh character. -/
theorem generatedFifthSignShortPacket01_source_character :
    ∀ j : Fin 56, ∀ f : Fin 64,
    (if generatedFifthSignShortPacket01Source j f = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket01Alpha j *
        generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket01Character j) f := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the correcting character against the genuine quadratic diagonal.
/-- Each correcting row is the exact Fourier-conjugate character. -/
theorem generatedFifthSignShortPacket01_correction_character :
    ∀ j : Fin 56, ∀ e : Fin 64,
    (if generatedFifthSignShortPacket01Correction j e = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket01Alpha j *
        (trialityIntegerDiagonal (generatedFifthEvenRootSign j) *
          trialityIntegerDiagonal
            (trialityXor (generatedFifthSignShortPacket01Character j)
              (generatedFifthEvenRootSign j)) *
          generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket01Character j) e) := by
  decide +kernel

/-- Exact character transport restores every original supported octad coefficient. -/
theorem generatedFifthSignShortPacket01_numerator (j : Fin 56) (e : Fin 64) :
    generatedFifthSignShortPacket01Numerator j e =
      8 * generatedFifthSignFourierCache e (generatedFifthEvenRootSign j) := by
  unfold generatedFifthSignShortPacket01Numerator
  simp_rw [generatedFifthSignShortPacket01_correction_character,
    generatedFifthSignShortPacket01_source_character,
    generatedFifth_sign_hadamard_cache, generatedFifth_sign_fourier_cache]
  exact generatedFifth_sign_fourier_character_signed _ (generatedFifthSignShortPacket01_alpha_sq j)
    (generatedFifthSignShortPacket01Character j) (generatedFifthEvenRootSign j) e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
