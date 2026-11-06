/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamFourth

/-! # Factory parts (tensor) of the identification Fourth[10]+ <-> Root8[25]+ (record r8f:R820+, e
= 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wR8fR820p_ht : wR8fR820pL.sden * (oddLZ 64 true wR8fR820pGX wR8fR820pL : ℚ) /
    ((tensorWordDenAll wR8fR820pG : ℚ) * 1) +
    (tdotM 64 (trialityTensorT 64 (!true) wR8fR820pHX) wR8fR820pGX : ℚ) / (2 * ((tensorWordDenAll
        wR8fR820pH : ℚ) * 32) * ((tensorWordDenAll wR8fR820pG : ℚ) * 1)) =
      (tdotM 64 wR8fR820pGX wR8fR820pGX : ℚ) / (((tensorWordDenAll wR8fR820pG : ℚ) * 1) *
          ((tensorWordDenAll wR8fR820pG : ℚ) * 1)) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
