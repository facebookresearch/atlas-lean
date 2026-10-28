/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV3pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV3pPO
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthMatF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF

/-! # Pairing parts (octads, matrix, pairs) of the Tenth identification T3+ (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem tv3p_hok : octPackOk 32 tv3pL = true :=
  OctadDense.octPackOk_of_chk 32 4 true tv3pL tv3pHC tv3pGC 251296 rfl tv3p_oct

/-- The octad part of the pairing. -/
theorem tv3p_hn : octSumZ 32 true tv3pL tv3pW = 251296 :=
  OctadDense.octSumZ_of_chk 32 4 true tv3pL tv3pW tv3pHC tv3pGC 251296 rfl rfl tv3p_oct

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem tv3p_hm : triMatF true tv3pL tv3pW = ((365 : ℚ) / 128) := by
  rw [triMatF_eq_ZI true tv3pL tv3pW (srcTenthMatZ.act tv3pH) (srcTenthMatZ.act tv3pG)
    (srcTenthMat_act_entryZ tv3pH) (srcTenthMat_act_entryZ tv3pG), ← MatZ.actF_eq tv3pH,
    ← MatZ.actF_eq tv3pG]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part of the pairing. -/
theorem tv3p_hp : pairSumQ true tv3pL tv3pW = ((89 : ℚ) / 8) := by
  rw [pairSumQ_eq_ZI true tv3pL tv3pW (srcTenthMatZ.act tv3pH) (srcTenthMat_act_entryZ tv3pH),
    ← MatZ.actF_eq tv3pH]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
