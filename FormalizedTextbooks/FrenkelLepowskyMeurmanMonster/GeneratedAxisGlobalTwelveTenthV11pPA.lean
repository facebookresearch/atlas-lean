/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV11pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV11pPO
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthMatF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF

/-! # Pairing parts (octads, matrix, pairs) of the Tenth identification T11+ (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem tv11p_hok : octPackOk 32 tv11pL = true :=
  OctadDense.octPackOk_of_chk 32 4 true tv11pL tv11pHC tv11pGC 251424 rfl tv11p_oct

/-- The octad part of the pairing. -/
theorem tv11p_hn : octSumZ 32 true tv11pL tv11pW = 251424 :=
  OctadDense.octSumZ_of_chk 32 4 true tv11pL tv11pW tv11pHC tv11pGC 251424 rfl rfl tv11p_oct

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem tv11p_hm : triMatF true tv11pL tv11pW = ((365 : ℚ) / 128) := by
  rw [triMatF_eq_ZI true tv11pL tv11pW (srcTenthMatZ.act tv11pH) (srcTenthMatZ.act tv11pG)
    (srcTenthMat_act_entryZ tv11pH) (srcTenthMat_act_entryZ tv11pG), ← MatZ.actF_eq tv11pH,
    ← MatZ.actF_eq tv11pG]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part of the pairing. -/
theorem tv11p_hp : pairSumQ true tv11pL tv11pW = ((85 : ℚ) / 8) := by
  rw [pairSumQ_eq_ZI true tv11pL tv11pW (srcTenthMatZ.act tv11pH) (srcTenthMat_act_entryZ tv11pH),
    ← MatZ.actF_eq tv11pH]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
