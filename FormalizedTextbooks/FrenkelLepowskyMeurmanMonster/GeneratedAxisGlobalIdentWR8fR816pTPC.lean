/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR816pTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR816pTTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Root8[22]+ <-> Root8[22]+ (record r8f:R816+, e
= 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The source short block as packed chunks. -/
theorem wR8fR816pT_LshC : wR8fR816pTL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR816pTHT0Labs, wR8fR816pTHT0Nums, 2048), (wR8fR816pTHT1Labs, wR8fR816pTHT1Nums, 2048),
    (wR8fR816pTHT2Labs, wR8fR816pTHT2Nums, 2048), (wR8fR816pTHT3Labs, wR8fR816pTHT3Nums, 2048),
    (wR8fR816pTHT4Labs, wR8fR816pTHT4Nums, 2048), (wR8fR816pTHT5Labs, wR8fR816pTHT5Nums, 2048),
    (wR8fR816pTHT6Labs, wR8fR816pTHT6Nums, 2048), (wR8fR816pTHT7Labs, wR8fR816pTHT7Nums, 2048),
    (wR8fR816pTHT8Labs, wR8fR816pTHT8Nums, 2048), (wR8fR816pTHT9Labs, wR8fR816pTHT9Nums, 2048),
    (wR8fR816pTHT10Labs, wR8fR816pTHT10Nums, 2048), (wR8fR816pTHT11Labs, wR8fR816pTHT11Nums,
    2048), (wR8fR816pTHT12Labs, wR8fR816pTHT12Nums, 2048), (wR8fR816pTHT13Labs,
    wR8fR816pTHT13Nums, 2048), (wR8fR816pTHT14Labs, wR8fR816pTHT14Nums, 2048),
    (wR8fR816pTHT15Labs, wR8fR816pTHT15Nums, 2048), (wR8fR816pTHT16Labs, wR8fR816pTHT16Nums,
    808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wR8fR816pT_nlchk : OddDense.oddChk 64 ((2 ^ 4 - 1) * 2 ^ 0) false true
    [(wR8fR816pTHT0Labs, wR8fR816pTHT0Nums, 2048), (wR8fR816pTHT1Labs, wR8fR816pTHT1Nums, 2048),
    (wR8fR816pTHT2Labs, wR8fR816pTHT2Nums, 2048), (wR8fR816pTHT3Labs, wR8fR816pTHT3Nums, 2048),
    (wR8fR816pTHT4Labs, wR8fR816pTHT4Nums, 2048), (wR8fR816pTHT5Labs, wR8fR816pTHT5Nums, 2048),
    (wR8fR816pTHT6Labs, wR8fR816pTHT6Nums, 2048), (wR8fR816pTHT7Labs, wR8fR816pTHT7Nums, 2048),
    (wR8fR816pTHT8Labs, wR8fR816pTHT8Nums, 2048), (wR8fR816pTHT9Labs, wR8fR816pTHT9Nums, 2048),
    (wR8fR816pTHT10Labs, wR8fR816pTHT10Nums, 2048), (wR8fR816pTHT11Labs, wR8fR816pTHT11Nums,
    2048), (wR8fR816pTHT12Labs, wR8fR816pTHT12Nums, 2048), (wR8fR816pTHT13Labs,
    wR8fR816pTHT13Nums, 2048), (wR8fR816pTHT14Labs, wR8fR816pTHT14Nums, 2048),
    (wR8fR816pTHT15Labs, wR8fR816pTHT15Nums, 2048), (wR8fR816pTHT16Labs, wR8fR816pTHT16Nums, 808)]
    wR8fR816pTGX0 (256000) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wR8fR816pT_nl : oddLZ 64 true wR8fR816pTGX0 wR8fR816pTL = 256000 :=
  OddDense.oddLZ_of_chk true wR8fR816pTL wR8fR816pTW _ wR8fR816pT_LshC (wR8fR816pTGX0_ten
      ((tensorWordDenAll wR8fR816pTG : ℚ) * 32)).symm (by decide +kernel)
    (by decide +kernel) wR8fR816pTGX0_bnd wR8fR816pT_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wR8fR816pT_v1 : tdotM 64 (trialityTensorT 64 (!true) wR8fR816pTHX0) wR8fR816pTGX0 = 128000
    := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wR8fR816pT_v2 : tdotM 64 wR8fR816pTGX0 wR8fR816pTGX0 = 128000 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wR8fR816pT_ht : wR8fR816pTL.sden * (oddLZ 64 true wR8fR816pTGX0 wR8fR816pTL : ℚ) /
    (((tensorWordDenAll wR8fR816pTG : ℚ) * 32) / 2 ^ 21) +
    (tdotM 64 (trialityTensorT 64 (!true) wR8fR816pTHX0) wR8fR816pTGX0 : ℚ) / (2 *
        (((tensorWordDenAll wR8fR816pTH : ℚ) * 32) / 2 ^ 20) * (((tensorWordDenAll wR8fR816pTG :
        ℚ) * 32) / 2 ^ 21)) =
      (tdotM 64 wR8fR816pTGX0 wR8fR816pTGX0 : ℚ) / ((((tensorWordDenAll wR8fR816pTG : ℚ) * 32) / 2
          ^ 21) * (((tensorWordDenAll wR8fR816pTG : ℚ) * 32) / 2 ^ 21)) := by
  rw [wR8fR816pT_nl, wR8fR816pT_v1, wR8fR816pT_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
