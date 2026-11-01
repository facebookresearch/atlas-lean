/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF64pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF64pPO
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthMatF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamFourth

/-! # Pairing parts (octads, matrix, pairs) of the Tenth identification T64+ (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem tf64p_hok : octPackOk 32 tf64pL = true :=
  OctadDense.octPackOk_of_chk 32 4 true tf64pL tf64pHC tf64pGC 68352 rfl tf64p_oct

/-- The octad part of the pairing. -/
theorem tf64p_hn : octSumZ 32 true tf64pL tf64pW = 68352 :=
  OctadDense.octSumZ_of_chk 32 4 true tf64pL tf64pW tf64pHC tf64pGC 68352 rfl rfl tf64p_oct

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem tf64p_hm : triMatF true tf64pL tf64pW = ((29 : ℚ) / 8) := by
  rw [triMatF_eq_ZI true tf64pL tf64pW (srcTenthMatZ.act tf64pH) (fourthSrcMatZ.act tf64pG)
    (srcTenthMat_act_entryZ tf64pH) (fourthSrcMat_act_entryZ tf64pG), ← MatZ.actF_eq tf64pH,
    ← MatZ.actF_eq tf64pG]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part of the pairing. -/
theorem tf64p_hp : pairSumQ true tf64pL tf64pW = (2 : ℚ) := by
  rw [pairSumQ_eq_ZI true tf64pL tf64pW (srcTenthMatZ.act tf64pH) (srcTenthMat_act_entryZ tf64pH),
    ← MatZ.actF_eq tf64pH]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
