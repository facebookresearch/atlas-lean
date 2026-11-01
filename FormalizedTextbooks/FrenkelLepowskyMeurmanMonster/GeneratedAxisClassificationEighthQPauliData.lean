/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPauliState

/-! Literal full Pauli coordinates at all seven original stages of the eighth word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

open scoped Matrix

/-- All source, successor and final coordinates retain the original central phases. -/
def generatedEighthSpinPauliCache : Fin 12 → Fin 8 → Q :=
![
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 14)
      (golayLabelCoefficients 1) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 14)
      (golayLabelCoefficients 240) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1008)
      (golayLabelCoefficients 0) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1008)
      (golayLabelCoefficients 0) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2966)
      (golayLabelCoefficients 1798) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3990)
      (golayLabelCoefficients 1036) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2972)
      (golayLabelCoefficients 2058) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 2) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 13)
      (golayLabelCoefficients 2) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3325)
      (golayLabelCoefficients 828) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3664)
      (golayLabelCoefficients 12) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 604)
      (golayLabelCoefficients 3084) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3060)
      (golayLabelCoefficients 3063) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3082)
      (golayLabelCoefficients 2061) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1026)
      (golayLabelCoefficients 1031) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 4) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 11)
      (golayLabelCoefficients 4) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1791)
      (golayLabelCoefficients 913) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1377)
      (golayLabelCoefficients 12) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 364)
      (golayLabelCoefficients 2050) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2797)
      (golayLabelCoefficients 3420) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2701)
      (golayLabelCoefficients 3409) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3726)
      (golayLabelCoefficients 2387) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 8) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 7)
      (golayLabelCoefficients 8) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1535)
      (golayLabelCoefficients 865) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1439)
      (golayLabelCoefficients 12) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 412)
      (golayLabelCoefficients 2051) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2419)
      (golayLabelCoefficients 3756) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2323)
      (golayLabelCoefficients 3745) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3358)
      (golayLabelCoefficients 2722) 0],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 16) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 16) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1040) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1310) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2049)
      (golayLabelCoefficients 1310) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2045)
      (golayLabelCoefficients 38) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1710)
      (golayLabelCoefficients 740) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 683)
      (golayLabelCoefficients 2789) 0],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 32) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 32) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 48) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 81) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 14)
      (golayLabelCoefficients 81) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 14)
      (golayLabelCoefficients 96) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1008)
      (golayLabelCoefficients 913) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1022)
      (golayLabelCoefficients 913) 0],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 64) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 64) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1152) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1679) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2063)
      (golayLabelCoefficients 1679) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2035)
      (golayLabelCoefficients 1793) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1374)
      (golayLabelCoefficients 1885) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2386)
      (golayLabelCoefficients 3932) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 128) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 128) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 192) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 161) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 14)
      (golayLabelCoefficients 161) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 14)
      (golayLabelCoefficients 0) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1008)
      (golayLabelCoefficients 240) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1008)
      (golayLabelCoefficients 240) 1],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 256) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 256) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 779) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 10) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 10)
      (golayLabelCoefficients 10) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2306)
      (golayLabelCoefficients 93) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3023)
      (golayLabelCoefficients 0) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 960)
      (golayLabelCoefficients 1039) 0],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 512) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 512) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 12) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 12) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 12)
      (golayLabelCoefficients 12) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 768)
      (golayLabelCoefficients 240) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 254)
      (golayLabelCoefficients 0) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 240)
      (golayLabelCoefficients 1) 0],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1024) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
      (golayLabelCoefficients 1024) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
      (golayLabelCoefficients 1265) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
      (golayLabelCoefficients 2044) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2060)
      (golayLabelCoefficients 1020) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2816)
      (golayLabelCoefficients 919) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2302)
      (golayLabelCoefficients 871) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 248)
      (golayLabelCoefficients 1894) 0],
  ![
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
      (golayLabelCoefficients 0) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1024) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 1265) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
      (golayLabelCoefficients 2044) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2060)
      (golayLabelCoefficients 2044) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2816)
      (golayLabelCoefficients 1894) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2302)
      (golayLabelCoefficients 1179) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2292)
      (golayLabelCoefficients 154) 1]
]

/-- Eleven selected original final generators. -/
def generatedEighthSpinPauliIndependent : Fin 11 → Fin 12 := ![0,1,2,3,4,5,6,7,8,9,10]

/-- Their literal final translation masks, verified against actual spin coordinates. -/
def generatedEighthSpinPauliTranslationMask : Fin 11 → ℕ :=
  ![2972,1026,3726,3358,683,1022,2386,1008,960,240,248]

/-- A literal binary left inverse for the eleven actual translation columns. -/
def generatedEighthSpinPauliLeftInverseMask : Fin 11 → ℕ :=
  ![1798,1264,1078,1222,1,2034,1009,1363,912,653,13]

/-- The original binary translation matrix decoded from twelve actual coordinates. -/
def generatedEighthSpinPauliTranslationMatrix : Matrix (Fin 12) (Fin 11) (ZMod 2) :=
  fun i j => monsterCo1GeometryBinaryMaskDecode (generatedEighthSpinPauliTranslationMask j) i

/-- The decoded original binary left inverse. -/
def generatedEighthSpinPauliLeftInverse : Matrix (Fin 11) (Fin 12) (ZMod 2) :=
  fun i j => monsterCo1GeometryBinaryMaskDecode (generatedEighthSpinPauliLeftInverseMask i) j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
