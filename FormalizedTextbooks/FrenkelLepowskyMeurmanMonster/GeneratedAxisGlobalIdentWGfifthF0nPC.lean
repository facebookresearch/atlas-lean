/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGfifthF0nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ

/-! # Factory parts (tensor) of the identification Fifth[0]- <-> Fifth[0]- (record gfifth:F0-, e =
-1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The fields of the target tensor are below `2^24`. -/
theorem wGfifthF0n_ylt : colsLtB 64 24 wGfifthF0nGX = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGfifthF0n_ht : wGfifthF0nL.sden * (oddLZ 64 false wGfifthF0nGX wGfifthF0nL : ℚ) /
    ((tensorWordDenAll wGfifthF0nG : ℚ) * 1) +
    (tdotM 64 (trialityTensorT 64 (!false) wGfifthF0nHX) wGfifthF0nGX : ℚ) / (2 *
        ((tensorWordDenAll wGfifthF0nH : ℚ) * 1) * ((tensorWordDenAll wGfifthF0nG : ℚ) * 1)) =
      (tdotM 64 wGfifthF0nGX wGfifthF0nGX : ℚ) / (((tensorWordDenAll wGfifthF0nG : ℚ) * 1) *
          ((tensorWordDenAll wGfifthF0nG : ℚ) * 1)) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
