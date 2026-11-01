/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26pTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Eighth[37]+ <-> Seventh[32]+ (record
goctad:E26+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGoctadE26p_ht : wGoctadE26pL.sden * (oddLZ 64 true wGoctadE26pGXn wGoctadE26pL : ℚ) /
    ((tensorWordDenAll wGoctadE26pG : ℚ) * srcSeventhD0) +
    (tdotM 64 (trialityTensorT 64 (!true) wGoctadE26pHXn) wGoctadE26pGXn : ℚ) / (2 *
        ((tensorWordDenAll wGoctadE26pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) *
        ((tensorWordDenAll wGoctadE26pG : ℚ) * srcSeventhD0)) =
      (tdotM 64 wGoctadE26pGXn wGoctadE26pGXn : ℚ) / (((tensorWordDenAll wGoctadE26pG : ℚ) *
          srcSeventhD0) * ((tensorWordDenAll wGoctadE26pG : ℚ) * srcSeventhD0)) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
