/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGtwelfthW30pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (tensor) of the identification Twelfth[30]- <-> Twelfth[30]+ (record
gtwelfth:W30+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGtwelfthW30p_ht : wGtwelfthW30pL.sden * (oddLZ 64 true wGtwelfthW30pGX wGtwelfthW30pL :
    ℚ) / ((tensorWordDenAll wGtwelfthW30pG : ℚ) * 32) +
    (tdotM 64 (trialityTensorT 64 (!true) wGtwelfthW30pHX) wGtwelfthW30pGX : ℚ) / (2 *
        ((tensorWordDenAll wGtwelfthW30pH : ℚ) * 32) * ((tensorWordDenAll wGtwelfthW30pG : ℚ) *
        32)) =
      (tdotM 64 wGtwelfthW30pGX wGtwelfthW30pGX : ℚ) / (((tensorWordDenAll wGtwelfthW30pG : ℚ) *
          32) * ((tensorWordDenAll wGtwelfthW30pG : ℚ) * 32)) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
