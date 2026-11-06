/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV18nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV18nPO
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthMatF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF

/-! # Pairing parts (octads, matrix, pairs) of the Tenth identification T18- (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem tv18n_hok : octPackOk 32 tv18nL = true :=
  OctadDense.octPackOk_of_chk 32 4 false tv18nL tv18nHC tv18nGC 251488 rfl tv18n_oct

/-- The octad part of the pairing. -/
theorem tv18n_hn : octSumZ 32 false tv18nL tv18nW = 251488 :=
  OctadDense.octSumZ_of_chk 32 4 false tv18nL tv18nW tv18nHC tv18nGC 251488 rfl rfl tv18n_oct

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem tv18n_hm : triMatF false tv18nL tv18nW = ((365 : ℚ) / 128) := by
  rw [triMatF_eq_ZI false tv18nL tv18nW (srcTenthMatZ.act tv18nH) (srcTenthMatZ.act tv18nG)
    (srcTenthMat_act_entryZ tv18nH) (srcTenthMat_act_entryZ tv18nG), ← MatZ.actF_eq tv18nH,
    ← MatZ.actF_eq tv18nG]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part of the pairing. -/
theorem tv18n_hp : pairSumQ false tv18nL tv18nW = ((83 : ℚ) / 8) := by
  rw [pairSumQ_eq_ZI false tv18nL tv18nW (srcTenthMatZ.act tv18nH) (srcTenthMat_act_entryZ tv18nH),
    ← MatZ.actF_eq tv18nH]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
