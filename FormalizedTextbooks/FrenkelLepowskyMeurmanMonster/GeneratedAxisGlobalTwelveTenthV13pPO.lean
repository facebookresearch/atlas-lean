/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV13pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOctadFastDense

/-! # Octad part of the Tenth identification T13+ (gtenth)

The dense octad check alone (minimal imports: the check peaks at about 13 GiB). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad part (packed octad transform, field width `32`). -/
theorem tv13p_oct : OctadDense.octSumChk 32 4 true tv13pHC tv13pGC 251296 = true := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
