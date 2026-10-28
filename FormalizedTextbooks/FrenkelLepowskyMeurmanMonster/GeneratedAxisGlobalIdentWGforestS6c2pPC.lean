/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS6c2pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamFourth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS6c2pTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Fourth[18]- <-> Sixth[3]+ (record
gforest:S6c2+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The source short block as packed chunks. -/
theorem wGforestS6c2p_LshC : wGforestS6c2pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGforestS6c2pHT0Labs, wGforestS6c2pHT0Nums, 2048), (wGforestS6c2pHT1Labs,
    wGforestS6c2pHT1Nums, 2048), (wGforestS6c2pHT2Labs, wGforestS6c2pHT2Nums, 2048),
    (wGforestS6c2pHT3Labs, wGforestS6c2pHT3Nums, 2048), (wGforestS6c2pHT4Labs,
    wGforestS6c2pHT4Nums, 2048), (wGforestS6c2pHT5Labs, wGforestS6c2pHT5Nums, 2048),
    (wGforestS6c2pHT6Labs, wGforestS6c2pHT6Nums, 2048), (wGforestS6c2pHT7Labs,
    wGforestS6c2pHT7Nums, 2048), (wGforestS6c2pHT8Labs, wGforestS6c2pHT8Nums, 2048),
    (wGforestS6c2pHT9Labs, wGforestS6c2pHT9Nums, 2048), (wGforestS6c2pHT10Labs,
    wGforestS6c2pHT10Nums, 2048), (wGforestS6c2pHT11Labs, wGforestS6c2pHT11Nums, 2048),
    (wGforestS6c2pHT12Labs, wGforestS6c2pHT12Nums, 2048), (wGforestS6c2pHT13Labs,
    wGforestS6c2pHT13Nums, 2048), (wGforestS6c2pHT14Labs, wGforestS6c2pHT14Nums, 1640)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGforestS6c2p_nlchk : OddDense.oddChk 64 ((2 ^ 4 - 1) * 2 ^ 0) false true
    [(wGforestS6c2pHT0Labs, wGforestS6c2pHT0Nums, 2048), (wGforestS6c2pHT1Labs,
    wGforestS6c2pHT1Nums, 2048), (wGforestS6c2pHT2Labs, wGforestS6c2pHT2Nums, 2048),
    (wGforestS6c2pHT3Labs, wGforestS6c2pHT3Nums, 2048), (wGforestS6c2pHT4Labs,
    wGforestS6c2pHT4Nums, 2048), (wGforestS6c2pHT5Labs, wGforestS6c2pHT5Nums, 2048),
    (wGforestS6c2pHT6Labs, wGforestS6c2pHT6Nums, 2048), (wGforestS6c2pHT7Labs,
    wGforestS6c2pHT7Nums, 2048), (wGforestS6c2pHT8Labs, wGforestS6c2pHT8Nums, 2048),
    (wGforestS6c2pHT9Labs, wGforestS6c2pHT9Nums, 2048), (wGforestS6c2pHT10Labs,
    wGforestS6c2pHT10Nums, 2048), (wGforestS6c2pHT11Labs, wGforestS6c2pHT11Nums, 2048),
    (wGforestS6c2pHT12Labs, wGforestS6c2pHT12Nums, 2048), (wGforestS6c2pHT13Labs,
    wGforestS6c2pHT13Nums, 2048), (wGforestS6c2pHT14Labs, wGforestS6c2pHT14Nums, 1640)]
    wGforestS6c2pGX0 (57344) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGforestS6c2p_nl : oddLZ 64 true wGforestS6c2pGX0 wGforestS6c2pL = 57344 :=
  OddDense.oddLZ_of_chk true wGforestS6c2pL wGforestS6c2pW _ wGforestS6c2p_LshC
      (wGforestS6c2pGX0_ten ((tensorWordDenAll wGforestS6c2pG : ℚ) * 1)).symm (by decide +kernel)
    (by decide +kernel) wGforestS6c2pGX0_bnd wGforestS6c2p_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGforestS6c2p_v1 : tdotM 64 (trialityTensorT 64 (!true) wGforestS6c2pHX0) wGforestS6c2pGX0
    = 114688 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGforestS6c2p_v2 : tdotM 64 wGforestS6c2pGX0 wGforestS6c2pGX0 = 114688 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGforestS6c2p_ht : wGforestS6c2pL.sden * (oddLZ 64 true wGforestS6c2pGX0 wGforestS6c2pL :
    ℚ) / (((tensorWordDenAll wGforestS6c2pG : ℚ) * 1) / 2 ^ 8) +
    (tdotM 64 (trialityTensorT 64 (!true) wGforestS6c2pHX0) wGforestS6c2pGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGforestS6c2pH : ℚ) * 32) / 2 ^ 8) * (((tensorWordDenAll
        wGforestS6c2pG : ℚ) * 1) / 2 ^ 8)) =
      (tdotM 64 wGforestS6c2pGX0 wGforestS6c2pGX0 : ℚ) / ((((tensorWordDenAll wGforestS6c2pG : ℚ)
          * 1) / 2 ^ 8) * (((tensorWordDenAll wGforestS6c2pG : ℚ) * 1) / 2 ^ 8)) := by
  rw [wGforestS6c2p_nl, wGforestS6c2p_v1, wGforestS6c2p_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
