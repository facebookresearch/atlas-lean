/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV59pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV59pPO
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF

/-! # Pairing parts (octads, matrix, pairs) of the Tenth identification T59+ (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem tv59p_hok : octPackOk 32 tv59pL = true :=
  OctadDense.octPackOk_of_chk 32 4 true tv59pL tv59pHC tv59pGC 251488 rfl tv59p_oct

/-- The octad part of the pairing. -/
theorem tv59p_hn : octSumZ 32 true tv59pL tv59pW = 251488 :=
  OctadDense.octSumZ_of_chk 32 4 true tv59pL tv59pW tv59pHC tv59pGC 251488 rfl rfl tv59p_oct

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem tv59p_hm : triMatF true tv59pL tv59pW = ((365 : ℚ) / 128) := by
  rw [triMatF_eq_ZI true tv59pL tv59pW (srcTenthMatZ.act tv59pH) (srcTenthMatZ.act tv59pG)
    (srcTenthMat_act_entryZ tv59pH) (srcTenthMat_act_entryZ tv59pG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part of the pairing. -/
theorem tv59p_hp : pairSumQ true tv59pL tv59pW = ((83 : ℚ) / 8) := by
  rw [pairSumQ_eq_ZI true tv59pL tv59pW (srcTenthMatZ.act tv59pH) (srcTenthMat_act_entryZ tv59pH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
