/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGfifthF12nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamFourth

/-! # Factory parts (tensor) of the identification Fifth[12]- <-> Fourth[2]- (record gfifth:F12-,
e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGfifthF12n_ht : wGfifthF12nL.sden * (oddLZ 64 false wGfifthF12nGX wGfifthF12nL : ℚ) /
    ((tensorWordDenAll wGfifthF12nG : ℚ) * 1) +
    (tdotM 64 (trialityTensorT 64 (!false) wGfifthF12nHX) wGfifthF12nGX : ℚ) / (2 *
        ((tensorWordDenAll wGfifthF12nH : ℚ) * 1) * ((tensorWordDenAll wGfifthF12nG : ℚ) * 1)) =
      (tdotM 64 wGfifthF12nGX wGfifthF12nGX : ℚ) / (((tensorWordDenAll wGfifthF12nG : ℚ) * 1) *
          ((tensorWordDenAll wGfifthF12nG : ℚ) * 1)) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
