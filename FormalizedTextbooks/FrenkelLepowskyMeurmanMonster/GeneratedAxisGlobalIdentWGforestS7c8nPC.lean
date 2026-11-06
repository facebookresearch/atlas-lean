/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c8nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c8nTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Eighth[13]+ <-> Seventh[14]- (record
gforest:S7c8-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The source short block as packed chunks. -/
theorem wGforestS7c8n_LshC : wGforestS7c8nL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGforestS7c8nHT0Labs, wGforestS7c8nHT0Nums, 2048), (wGforestS7c8nHT1Labs,
    wGforestS7c8nHT1Nums, 2048), (wGforestS7c8nHT2Labs, wGforestS7c8nHT2Nums, 2048),
    (wGforestS7c8nHT3Labs, wGforestS7c8nHT3Nums, 2048), (wGforestS7c8nHT4Labs,
    wGforestS7c8nHT4Nums, 2048), (wGforestS7c8nHT5Labs, wGforestS7c8nHT5Nums, 2048),
    (wGforestS7c8nHT6Labs, wGforestS7c8nHT6Nums, 2048), (wGforestS7c8nHT7Labs,
    wGforestS7c8nHT7Nums, 2048), (wGforestS7c8nHT8Labs, wGforestS7c8nHT8Nums, 2048),
    (wGforestS7c8nHT9Labs, wGforestS7c8nHT9Nums, 2048), (wGforestS7c8nHT10Labs,
    wGforestS7c8nHT10Nums, 2048), (wGforestS7c8nHT11Labs, wGforestS7c8nHT11Nums, 2048),
    (wGforestS7c8nHT12Labs, wGforestS7c8nHT12Nums, 2048), (wGforestS7c8nHT13Labs,
    wGforestS7c8nHT13Nums, 1000)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGforestS7c8n_nlchk : OddDense.oddChk 72 ((2 ^ 4 - 1) * 2 ^ 0) true false
    [(wGforestS7c8nHT0Labs, wGforestS7c8nHT0Nums, 2048), (wGforestS7c8nHT1Labs,
    wGforestS7c8nHT1Nums, 2048), (wGforestS7c8nHT2Labs, wGforestS7c8nHT2Nums, 2048),
    (wGforestS7c8nHT3Labs, wGforestS7c8nHT3Nums, 2048), (wGforestS7c8nHT4Labs,
    wGforestS7c8nHT4Nums, 2048), (wGforestS7c8nHT5Labs, wGforestS7c8nHT5Nums, 2048),
    (wGforestS7c8nHT6Labs, wGforestS7c8nHT6Nums, 2048), (wGforestS7c8nHT7Labs,
    wGforestS7c8nHT7Nums, 2048), (wGforestS7c8nHT8Labs, wGforestS7c8nHT8Nums, 2048),
    (wGforestS7c8nHT9Labs, wGforestS7c8nHT9Nums, 2048), (wGforestS7c8nHT10Labs,
    wGforestS7c8nHT10Nums, 2048), (wGforestS7c8nHT11Labs, wGforestS7c8nHT11Nums, 2048),
    (wGforestS7c8nHT12Labs, wGforestS7c8nHT12Nums, 2048), (wGforestS7c8nHT13Labs,
    wGforestS7c8nHT13Nums, 1000)] wGforestS7c8nGX0 (64768) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGforestS7c8n_nl : oddLZ 72 false wGforestS7c8nGX0 wGforestS7c8nL = 64768 :=
  OddDense.oddLZ_of_chk false wGforestS7c8nL wGforestS7c8nW _ wGforestS7c8n_LshC
      (wGforestS7c8nGX0_ten ((tensorWordDenAll wGforestS7c8nG : ℚ) * (2 * ((tensorWordDenAll
      srcEighthH : ℚ) * 1)))).symm (by decide +kernel)
    (by decide +kernel) wGforestS7c8nGX0_bnd wGforestS7c8n_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGforestS7c8n_v1 : tdotM 72 (trialityTensorT 72 (!false) wGforestS7c8nHX0)
    wGforestS7c8nGX0 = 124416 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGforestS7c8n_v2 : tdotM 72 wGforestS7c8nGX0 wGforestS7c8nGX0 = 126976 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGforestS7c8n_ht : wGforestS7c8nL.sden * (oddLZ 72 false wGforestS7c8nGX0 wGforestS7c8nL :
    ℚ) / (((tensorWordDenAll wGforestS7c8nG : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))
    / 2 ^ 33) +
    (tdotM 72 (trialityTensorT 72 (!false) wGforestS7c8nHX0) wGforestS7c8nGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGforestS7c8nH : ℚ) * srcSeventhD0) / 2 ^ 20) * (((tensorWordDenAll
        wGforestS7c8nG : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 33)) =
      (tdotM 72 wGforestS7c8nGX0 wGforestS7c8nGX0 : ℚ) / ((((tensorWordDenAll wGforestS7c8nG : ℚ)
          * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 33) * (((tensorWordDenAll
          wGforestS7c8nG : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 33)) := by
  rw [wGforestS7c8n_nl, wGforestS7c8n_v1, wGforestS7c8n_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
