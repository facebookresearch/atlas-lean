/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignFourierCache

/-! A bounded integer short-coordinate packet for one original corrected Golay sign word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/-- Bitmasks of the original source Q-code characters on each actual outgoing family. -/
def generatedFifthSignShortPacket00SourceMasks : Fin 56 → ℕ :=
  ![7608384715226507670, 0, 7378753924479149670, 7378753924479149670,
    7378753924479149670, 7378753924479149670, 7378753924479149670, 7378753924479149670,
    7378753924479149670, 7378753924479149670, 7608384715226507670, 0,
    0, 7608384715226507670, 11068046444225730969, 11068046444225730969,
    11068046444225730969, 11068046444225730969, 11068046444225730969, 11068046444225730969,
    11068046444225730969, 11068046444225730969, 0, 7608384715226507670,
    7608384715226507670, 7608384715226507670, 11068046444225730969, 11068046444225730969,
    11068046444225730969, 11068046444225730969, 7608384715226507670, 7608384715226507670,
    7608384715226507670, 7608384715226507670, 11068046444225730969, 11068046444225730969,
    11068046444225730969, 11068046444225730969, 7608384715226507670, 7608384715226507670,
    7608384715226507670, 7608384715226507670, 11068046444225730969, 11068046444225730969,
    11068046444225730969, 11068046444225730969, 7608384715226507670, 7608384715226507670,
    7608384715226507670, 7608384715226507670, 11068046444225730969, 11068046444225730969,
    11068046444225730969, 11068046444225730969, 7608384715226507670, 7608384715226507670]

/-- Original source Q-code characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket00Source (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket00SourceMasks j).testBit e.val then 1 else 0

/-- Bitmasks of the original correcting Q characters on each actual outgoing family. -/
def generatedFifthSignShortPacket00CorrectionMasks : Fin 56 → ℕ :=
  ![10838359358483043945, 0, 7378753924479149670, 11067990149230401945,
    11067990149230401945, 7378753924479149670, 11067990149230401945, 7378753924479149670,
    7378753924479149670, 11067990149230401945, 10838359358483043945, 0,
    0, 10838359358483043945, 11068046444225730969, 7378697629483820646,
    11068046444225730969, 7378697629483820646, 11068046444225730969, 7378697629483820646,
    11068046444225730969, 7378697629483820646, 0, 10838359358483043945,
    10838359358483043945, 7608384715226507670, 7378697629483820646, 7378697629483820646,
    11068046444225730969, 11068046444225730969, 10838359358483043945, 7608384715226507670,
    10838359358483043945, 7608384715226507670, 7378697629483820646, 7378697629483820646,
    11068046444225730969, 11068046444225730969, 10838359358483043945, 7608384715226507670,
    10838359358483043945, 7608384715226507670, 7378697629483820646, 7378697629483820646,
    11068046444225730969, 11068046444225730969, 10838359358483043945, 7608384715226507670,
    7608384715226507670, 10838359358483043945, 11068046444225730969, 11068046444225730969,
    7378697629483820646, 7378697629483820646, 7608384715226507670, 10838359358483043945]

/-- Original correcting Q characters in the actual fifth-octad families. -/
def generatedFifthSignShortPacket00Correction (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  if (generatedFifthSignShortPacket00CorrectionMasks j).testBit e.val then 1 else 0

/-- Sixty-four times the corrected original short coefficient, omitting its common input sign. -/
def generatedFifthSignShortPacket00Numerator (j : Fin 56) (e : Fin 64) : ℤ :=
  (if generatedFifthSignShortPacket00Correction j e = 0 then 1 else -1) *
    ∑ f : Fin 64, generatedFifthSignFourierCache f e *
      (if generatedFifthSignShortPacket00Source j f = 0 then 1 else -1) *
      generatedFifthSignFourierCache (generatedFifthEvenRootSign j) f

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check all 3584 signed DH convolutions for this actual source word.
/-- The displayed full integer convolution restores every original supported octad coefficient. -/
theorem generatedFifthSignShortPacket00_numerator : ∀ j : Fin 56, ∀ e : Fin 64,
    generatedFifthSignShortPacket00Numerator j e =
      8 * generatedFifthSignFourierCache e (generatedFifthEvenRootSign j) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
