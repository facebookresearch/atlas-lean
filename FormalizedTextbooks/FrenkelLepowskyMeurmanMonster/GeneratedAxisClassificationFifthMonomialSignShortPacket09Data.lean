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
def generatedFifthSignShortPacket09SourceMasks : Fin 56 → ℕ :=
  ![10838310072981296745, 10838310072981296745, 3689348814741910323, 3689348814741910323,
    3689348814741910323, 3689348814741910323, 3689348814741910323, 3689348814741910323,
    3689348814741910323, 3689348814741910323, 14714328930390887475, 14714328930390887475,
    6510698342184737370, 11936045732788001370, 14714328927833961420, 11936045732788001370,
    11936045732788001370, 14714328927833961420, 14714328927833961420, 11936045732788001370,
    11936045732788001370, 14714328927833961420, 11067990150089369190, 14714328927833961420,
    3689348814741910323, 14757226373981654220, 11068046443366737510, 11068046443366737510,
    4294967295, 4294967295, 6148914691236517205, 12297735557480819370,
    4294967295, 4294967295, 4378557926219170620, 12297829381041378645,
    6531808642057217370, 14757395256390660915, 11068046443366737510, 11068046443366737510,
    4294967295, 4294967295, 12297829381041378645, 4378557926219170620,
    14757395256390660915, 6531808642057217370, 11068046443366737510, 11068046443366737510,
    4378557928475212995, 14068334001739580220, 7608433999976240745, 7608433999976240745,
    17298062221247451120, 17298062221247451120, 6531808643310574245, 11915017572901889370]

/-- Original source Q-code characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket09Source (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket09SourceMasks j).testBit e.val then 1 else 0

/-- Bitmasks of the original correcting Q characters on each actual outgoing family. -/
def generatedFifthSignShortPacket09CorrectionMasks : Fin 56 → ℕ :=
  ![7608434000728254870, 10838310072981296745, 3689348814741910323, 14757395258967641292,
    14757395258967641292, 3689348814741910323, 14757395258967641292, 3689348814741910323,
    3689348814741910323, 14757395258967641292, 3732415143318664140, 14714328930390887475,
    6510698342184737370, 6510698340921550245, 14714328927833961420, 6510698340921550245,
    11936045732788001370, 3732415145875590195, 14714328927833961420, 6510698340921550245,
    11936045732788001370, 3732415145875590195, 11067990150089369190, 3732415145875590195,
    14757395258967641292, 14757226373981654220, 7378697630342814105, 7378697630342814105,
    4294967295, 4294967295, 12297829382473034410, 12297735557480819370,
    18446744069414584320, 4294967295, 14068186147490380995, 6148914692668172970,
    6531808642057217370, 14757395256390660915, 7378697630342814105, 11068046443366737510,
    18446744069414584320, 4294967295, 6148914692668172970, 14068186147490380995,
    14757395256390660915, 6531808642057217370, 7378697630342814105, 11068046443366737510,
    4378557928475212995, 4378410071969971395, 7608433999976240745, 7608433999976240745,
    1148681852462100495, 1148681852462100495, 6531808643310574245, 6531726500807662245]

/-- Original correcting Q characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket09Correction (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket09CorrectionMasks j).testBit e.val then 1 else 0

/-- Sixty-four times the corrected original short coefficient, omitting its common input sign. -/
def generatedFifthSignShortPacket09Numerator (j : Fin 56) (e : Fin 64) : ℤ :=
  (if generatedFifthSignShortPacket09Correction j e = 0 then 1 else -1) *
    ∑ f : Fin 64, generatedFifthSignFourierCache f e *
      (if generatedFifthSignShortPacket09Source j f = 0 then 1 else -1) *
      generatedFifthSignFourierCache (generatedFifthEvenRootSign j) f

/-- Exact character label of the displayed source row. -/
def generatedFifthSignShortPacket09Character : Fin 56 → Fin 64 :=
  ![
    63, 63, 61, 61, 61, 61, 61, 61,
    61, 61, 10, 10, 53, 42, 21, 42,
    42, 21, 21, 42, 42, 21, 44, 21,
    61, 13, 28, 28, 31, 31, 62, 14,
    31, 31, 30, 33, 29, 34, 28, 28,
    31, 31, 33, 30, 34, 29, 28, 28,
    1, 49, 32, 32, 35, 35, 2, 50]

/-- The common sign of a source character row. -/
def generatedFifthSignShortPacket09Alpha (j : Fin 56) : ℤ :=
  if generatedFifthSignShortPacket09Source j 0 = 0 then 1 else -1

/-- The common sign is a unit of square one. -/
theorem generatedFifthSignShortPacket09_alpha_sq (j : Fin 56) :
    generatedFifthSignShortPacket09Alpha j * generatedFifthSignShortPacket09Alpha j = 1 := by
  unfold generatedFifthSignShortPacket09Alpha
  split <;> norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the displayed characters, with no Fourier sum to normalize.
/-- Each displayed source row is its stated genuine Walsh character. -/
theorem generatedFifthSignShortPacket09_source_character :
    ∀ j : Fin 56, ∀ f : Fin 64,
    (if generatedFifthSignShortPacket09Source j f = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket09Alpha j *
        generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket09Character j) f := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the correcting character against the genuine quadratic diagonal.
/-- Each correcting row is the exact Fourier-conjugate character. -/
theorem generatedFifthSignShortPacket09_correction_character :
    ∀ j : Fin 56, ∀ e : Fin 64,
    (if generatedFifthSignShortPacket09Correction j e = 0 then (1 : ℤ) else -1) =
      generatedFifthSignShortPacket09Alpha j *
        (trialityIntegerDiagonal (generatedFifthEvenRootSign j) *
          trialityIntegerDiagonal
            (trialityXor (generatedFifthSignShortPacket09Character j)
              (generatedFifthEvenRootSign j)) *
          generatedFifthSignHadamardCache
          (generatedFifthSignShortPacket09Character j) e) := by
  decide +kernel

/-- Exact character transport restores every original supported octad coefficient. -/
theorem generatedFifthSignShortPacket09_numerator (j : Fin 56) (e : Fin 64) :
    generatedFifthSignShortPacket09Numerator j e =
      8 * generatedFifthSignFourierCache e (generatedFifthEvenRootSign j) := by
  unfold generatedFifthSignShortPacket09Numerator
  simp_rw [generatedFifthSignShortPacket09_correction_character,
    generatedFifthSignShortPacket09_source_character,
    generatedFifth_sign_hadamard_cache, generatedFifth_sign_fourier_cache]
  exact generatedFifth_sign_fourier_character_signed _ (generatedFifthSignShortPacket09_alpha_sq j)
    (generatedFifthSignShortPacket09Character j) (generatedFifthEvenRootSign j) e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
