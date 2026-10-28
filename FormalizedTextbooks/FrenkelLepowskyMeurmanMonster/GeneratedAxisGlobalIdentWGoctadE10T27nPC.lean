/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE10T27nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE10T27nTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Eighth[14]- <-> Tenth[55]- (record
goctad:E10@T27-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The source short block as packed chunks. -/
theorem wGoctadE10T27n_LshC : wGoctadE10T27nL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE10T27nHT0Labs, wGoctadE10T27nHT0Nums, 2048), (wGoctadE10T27nHT1Labs,
    wGoctadE10T27nHT1Nums, 2048), (wGoctadE10T27nHT2Labs, wGoctadE10T27nHT2Nums, 2048),
    (wGoctadE10T27nHT3Labs, wGoctadE10T27nHT3Nums, 2048), (wGoctadE10T27nHT4Labs,
    wGoctadE10T27nHT4Nums, 2048), (wGoctadE10T27nHT5Labs, wGoctadE10T27nHT5Nums, 2048),
    (wGoctadE10T27nHT6Labs, wGoctadE10T27nHT6Nums, 2048), (wGoctadE10T27nHT7Labs,
    wGoctadE10T27nHT7Nums, 2048), (wGoctadE10T27nHT8Labs, wGoctadE10T27nHT8Nums, 2048),
    (wGoctadE10T27nHT9Labs, wGoctadE10T27nHT9Nums, 2048), (wGoctadE10T27nHT10Labs,
    wGoctadE10T27nHT10Nums, 2048), (wGoctadE10T27nHT11Labs, wGoctadE10T27nHT11Nums, 2048),
    (wGoctadE10T27nHT12Labs, wGoctadE10T27nHT12Nums, 2048), (wGoctadE10T27nHT13Labs,
    wGoctadE10T27nHT13Nums, 2048), (wGoctadE10T27nHT14Labs, wGoctadE10T27nHT14Nums, 2048),
    (wGoctadE10T27nHT15Labs, wGoctadE10T27nHT15Nums, 2048), (wGoctadE10T27nHT16Labs,
    wGoctadE10T27nHT16Nums, 2048), (wGoctadE10T27nHT17Labs, wGoctadE10T27nHT17Nums, 2048),
    (wGoctadE10T27nHT18Labs, wGoctadE10T27nHT18Nums, 2048), (wGoctadE10T27nHT19Labs,
    wGoctadE10T27nHT19Nums, 2048), (wGoctadE10T27nHT20Labs, wGoctadE10T27nHT20Nums, 2048),
    (wGoctadE10T27nHT21Labs, wGoctadE10T27nHT21Nums, 668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGoctadE10T27n_nlchk : OddDense.oddChk 64 ((2 ^ 4 - 1) * 2 ^ 0) true false
    [(wGoctadE10T27nHT0Labs, wGoctadE10T27nHT0Nums, 2048), (wGoctadE10T27nHT1Labs,
    wGoctadE10T27nHT1Nums, 2048), (wGoctadE10T27nHT2Labs, wGoctadE10T27nHT2Nums, 2048),
    (wGoctadE10T27nHT3Labs, wGoctadE10T27nHT3Nums, 2048), (wGoctadE10T27nHT4Labs,
    wGoctadE10T27nHT4Nums, 2048), (wGoctadE10T27nHT5Labs, wGoctadE10T27nHT5Nums, 2048),
    (wGoctadE10T27nHT6Labs, wGoctadE10T27nHT6Nums, 2048), (wGoctadE10T27nHT7Labs,
    wGoctadE10T27nHT7Nums, 2048), (wGoctadE10T27nHT8Labs, wGoctadE10T27nHT8Nums, 2048),
    (wGoctadE10T27nHT9Labs, wGoctadE10T27nHT9Nums, 2048), (wGoctadE10T27nHT10Labs,
    wGoctadE10T27nHT10Nums, 2048), (wGoctadE10T27nHT11Labs, wGoctadE10T27nHT11Nums, 2048),
    (wGoctadE10T27nHT12Labs, wGoctadE10T27nHT12Nums, 2048), (wGoctadE10T27nHT13Labs,
    wGoctadE10T27nHT13Nums, 2048), (wGoctadE10T27nHT14Labs, wGoctadE10T27nHT14Nums, 2048),
    (wGoctadE10T27nHT15Labs, wGoctadE10T27nHT15Nums, 2048), (wGoctadE10T27nHT16Labs,
    wGoctadE10T27nHT16Nums, 2048), (wGoctadE10T27nHT17Labs, wGoctadE10T27nHT17Nums, 2048),
    (wGoctadE10T27nHT18Labs, wGoctadE10T27nHT18Nums, 2048), (wGoctadE10T27nHT19Labs,
    wGoctadE10T27nHT19Nums, 2048), (wGoctadE10T27nHT20Labs, wGoctadE10T27nHT20Nums, 2048),
    (wGoctadE10T27nHT21Labs, wGoctadE10T27nHT21Nums, 668)] wGoctadE10T27nGX0 (65024) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGoctadE10T27n_nl : oddLZ 64 false wGoctadE10T27nGX0 wGoctadE10T27nL = 65024 :=
  OddDense.oddLZ_of_chk false wGoctadE10T27nL wGoctadE10T27nW _ wGoctadE10T27n_LshC
      (wGoctadE10T27nGX0_ten ((tensorWordDenAll wGoctadE10T27nG : ℚ) * 32)).symm (by
      decide +kernel)
    (by decide +kernel) wGoctadE10T27nGX0_bnd wGoctadE10T27n_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGoctadE10T27n_v1 : tdotM 64 (trialityTensorT 64 (!false) wGoctadE10T27nHX0)
    wGoctadE10T27nGX0 = 126976 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGoctadE10T27n_v2 : tdotM 64 wGoctadE10T27nGX0 wGoctadE10T27nGX0 = 128512 := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGoctadE10T27n_ht : wGoctadE10T27nL.sden * (oddLZ 64 false wGoctadE10T27nGX0
    wGoctadE10T27nL : ℚ) / (((tensorWordDenAll wGoctadE10T27nG : ℚ) * 32) / 2 ^ 21) +
    (tdotM 64 (trialityTensorT 64 (!false) wGoctadE10T27nHX0) wGoctadE10T27nGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGoctadE10T27nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))
        / 2 ^ 25) * (((tensorWordDenAll wGoctadE10T27nG : ℚ) * 32) / 2 ^ 21)) =
      (tdotM 64 wGoctadE10T27nGX0 wGoctadE10T27nGX0 : ℚ) / ((((tensorWordDenAll wGoctadE10T27nG :
          ℚ) * 32) / 2 ^ 21) * (((tensorWordDenAll wGoctadE10T27nG : ℚ) * 32) / 2 ^ 21)) := by
  rw [wGoctadE10T27n_nl, wGoctadE10T27n_v1, wGoctadE10T27n_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
