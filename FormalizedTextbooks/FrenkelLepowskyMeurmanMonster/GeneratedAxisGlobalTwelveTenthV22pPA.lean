/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV22pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV22pPO
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthMatF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF

/-! # Pairing parts (octads, matrix, pairs) of the Tenth identification T22+ (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem tv22p_hok : octPackOk 32 tv22pL = true :=
  OctadDense.octPackOk_of_chk 32 4 true tv22pL tv22pHC tv22pGC 251424 rfl tv22p_oct

/-- The octad part of the pairing. -/
theorem tv22p_hn : octSumZ 32 true tv22pL tv22pW = 251424 :=
  OctadDense.octSumZ_of_chk 32 4 true tv22pL tv22pW tv22pHC tv22pGC 251424 rfl rfl tv22p_oct

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem tv22p_hm : triMatF true tv22pL tv22pW = ((365 : ℚ) / 128) := by
  rw [triMatF_eq_ZI true tv22pL tv22pW (srcTenthMatZ.act tv22pH) (srcTenthMatZ.act tv22pG)
    (srcTenthMat_act_entryZ tv22pH) (srcTenthMat_act_entryZ tv22pG), ← MatZ.actF_eq tv22pH,
    ← MatZ.actF_eq tv22pG]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part of the pairing. -/
theorem tv22p_hp : pairSumQ true tv22pL tv22pW = ((85 : ℚ) / 8) := by
  rw [pairSumQ_eq_ZI true tv22pL tv22pW (srcTenthMatZ.act tv22pH) (srcTenthMat_act_entryZ tv22pH),
    ← MatZ.actF_eq tv22pH]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
