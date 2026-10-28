/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c14pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c14pTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Eighth[27]+ <-> Seventh[22]+ (record
gforest:S7c14+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGforestS7c14p_ht : wGforestS7c14pL.sden * (oddLZ 64 true wGforestS7c14pGX0
    wGforestS7c14pL : ℚ) / (((tensorWordDenAll wGforestS7c14pG : ℚ) * (2 * ((tensorWordDenAll
    srcEighthH : ℚ) * 1))) / 2 ^ 25) +
    (tdotM 64 (trialityTensorT 64 (!true) wGforestS7c14pHX0) wGforestS7c14pGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGforestS7c14pH : ℚ) * srcSeventhD0) / 2 ^ 20) * (((tensorWordDenAll
        wGforestS7c14pG : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 25)) =
      (tdotM 64 wGforestS7c14pGX0 wGforestS7c14pGX0 : ℚ) / ((((tensorWordDenAll wGforestS7c14pG :
          ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 25) * (((tensorWordDenAll
          wGforestS7c14pG : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 25)) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
