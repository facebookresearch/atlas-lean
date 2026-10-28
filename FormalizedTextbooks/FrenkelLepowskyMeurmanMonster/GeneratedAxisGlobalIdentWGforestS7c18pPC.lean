/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c18pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamFourth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c18pTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Fourth[13]- <-> Seventh[27]+ (record
gforest:S7c18+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGforestS7c18p_ht : wGforestS7c18pL.sden * (oddLZ 64 true wGforestS7c18pGX0
    wGforestS7c18pL : ℚ) / (((tensorWordDenAll wGforestS7c18pG : ℚ) * 1) / 2 ^ 5) +
    (tdotM 64 (trialityTensorT 64 (!true) wGforestS7c18pHX0) wGforestS7c18pGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGforestS7c18pH : ℚ) * srcSeventhD0) / 2 ^ 16) * (((tensorWordDenAll
        wGforestS7c18pG : ℚ) * 1) / 2 ^ 5)) =
      (tdotM 64 wGforestS7c18pGX0 wGforestS7c18pGX0 : ℚ) / ((((tensorWordDenAll wGforestS7c18pG :
          ℚ) * 1) / 2 ^ 5) * (((tensorWordDenAll wGforestS7c18pG : ℚ) * 1) / 2 ^ 5)) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
