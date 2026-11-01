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
def generatedFifthSignShortPacket02SourceMasks : Fin 56 → ℕ :=
  ![7608384715226507670, 7608384715226507670, 1148681856222171120, 1148681856222171120,
    1148681856222171120, 1148681856222171120, 1148681856222171120, 1148681856222171120,
    1148681856222171120, 1148681856222171120, 7608384715226507670, 7608384715226507670,
    7608384715226507670, 7608384715226507670, 7378753924479149670, 7378753924479149670,
    7378753924479149670, 7378753924479149670, 7378753924479149670, 7378753924479149670,
    7378753924479149670, 7378753924479149670, 7608384715226507670, 7608384715226507670,
    7378753924479149670, 7378753924479149670, 7378753924479149670, 7378753924479149670,
    7378753924479149670, 7378753924479149670, 7378753924479149670, 7378753924479149670,
    1148681856222171120, 1148681856222171120, 1148681856222171120, 1148681856222171120,
    1148681856222171120, 1148681856222171120, 1148681856222171120, 1148681856222171120,
    1148681856222171120, 1148681856222171120, 1148681856222171120, 1148681856222171120,
    1148681856222171120, 1148681856222171120, 1148681856222171120, 1148681856222171120,
    7378753924479149670, 7378753924479149670, 7378753924479149670, 7378753924479149670,
    7378753924479149670, 7378753924479149670, 7378753924479149670, 7378753924479149670]

/-- Original source Q-code characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket02Source (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket02SourceMasks j).testBit e.val then 1 else 0

/-- Bitmasks of the original correcting Q characters on each actual outgoing family. -/
def generatedFifthSignShortPacket02CorrectionMasks : Fin 56 → ℕ :=
  ![10838359358483043945, 10838359358483043945, 1148681856222171120, 1148681856222171120,
    17298062217487380495, 17298062217487380495, 17298062217487380495, 17298062217487380495,
    1148681856222171120, 1148681856222171120, 10838359358483043945, 10838359358483043945,
    10838359358483043945, 10838359358483043945, 7378753924479149670, 7378753924479149670,
    11067990149230401945, 11067990149230401945, 11067990149230401945, 11067990149230401945,
    7378753924479149670, 7378753924479149670, 10838359358483043945, 10838359358483043945,
    11067990149230401945, 7378753924479149670, 11067990149230401945, 7378753924479149670,
    7378753924479149670, 11067990149230401945, 7378753924479149670, 11067990149230401945,
    17298062217487380495, 1148681856222171120, 17298062217487380495, 1148681856222171120,
    1148681856222171120, 17298062217487380495, 1148681856222171120, 17298062217487380495,
    1148681856222171120, 17298062217487380495, 1148681856222171120, 17298062217487380495,
    17298062217487380495, 1148681856222171120, 17298062217487380495, 1148681856222171120,
    7378753924479149670, 11067990149230401945, 7378753924479149670, 11067990149230401945,
    11067990149230401945, 7378753924479149670, 11067990149230401945, 7378753924479149670]

/-- Original correcting Q characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket02Correction (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket02CorrectionMasks j).testBit e.val then 1 else 0

/-- Sixty-four times the corrected original short coefficient, omitting its common input sign. -/
def generatedFifthSignShortPacket02Numerator (j : Fin 56) (e : Fin 64) : ℤ :=
  (if generatedFifthSignShortPacket02Correction j e = 0 then 1 else -1) *
    ∑ f : Fin 64, generatedFifthSignFourierCache f e *
      (if generatedFifthSignShortPacket02Source j f = 0 then 1 else -1) *
      generatedFifthSignFourierCache (generatedFifthEvenRootSign j) f

/-- Exact character label of the displayed source row. -/
def generatedFifthSignShortPacket02Character : Fin 56 → Fin 64 :=
  ![
    15, 15, 60, 60, 60, 60, 60, 60,
    60, 60, 15, 15, 15, 15, 51, 51,
    51, 51, 51, 51, 51, 51, 15, 15,
    51, 51, 51, 51, 51, 51, 51, 51,
    60, 60, 60, 60, 60, 60, 60, 60,
    60, 60, 60, 60, 60, 60, 60, 60,
    51, 51, 51, 51, 51, 51, 51, 51]

/-- The common sign of a source character row. -/
def generatedFifthSignShortPacket02Alpha (j : Fin 56) : ℤ :=
  if generatedFifthSignShortPacket02Source j 0 = 0 then 1 else -1

/-- The common sign is a unit of square one. -/
theorem generatedFifthSignShortPacket02_alpha_sq (j : Fin 56) :
    generatedFifthSignShortPacket02Alpha j * generatedFifthSignShortPacket02Alpha j = 1 := by
  unfold generatedFifthSignShortPacket02Alpha
  split <;> norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the displayed characters, with no Fourier sum to normalize.
/-- Each displayed source row is its stated genuine Walsh character. -/
theorem generatedFifthSignShortPacket02_source_character :
    ∀ j : Fin 56, ∀ f : Fin 64,
    (if generatedFifthSignShortPacket02Source j f = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket02Alpha j *
        generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket02Character j) f := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the correcting character against the genuine quadratic diagonal.
/-- Each correcting row is the exact Fourier-conjugate character. -/
theorem generatedFifthSignShortPacket02_correction_character :
    ∀ j : Fin 56, ∀ e : Fin 64,
    (if generatedFifthSignShortPacket02Correction j e = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket02Alpha j *
        (trialityIntegerDiagonal (generatedFifthEvenRootSign j) *
          trialityIntegerDiagonal
            (trialityXor (generatedFifthSignShortPacket02Character j)
              (generatedFifthEvenRootSign j)) *
          generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket02Character j) e) := by
  decide +kernel

/-- Exact character transport restores every original supported octad coefficient. -/
theorem generatedFifthSignShortPacket02_numerator (j : Fin 56) (e : Fin 64) :
    generatedFifthSignShortPacket02Numerator j e =
      8 * generatedFifthSignFourierCache e (generatedFifthEvenRootSign j) := by
  unfold generatedFifthSignShortPacket02Numerator
  simp_rw [generatedFifthSignShortPacket02_correction_character,
    generatedFifthSignShortPacket02_source_character,
    generatedFifth_sign_hadamard_cache, generatedFifth_sign_fourier_cache]
  exact generatedFifth_sign_fourier_character_signed _ (generatedFifthSignShortPacket02_alpha_sq j)
    (generatedFifthSignShortPacket02Character j) (generatedFifthEvenRootSign j) e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
