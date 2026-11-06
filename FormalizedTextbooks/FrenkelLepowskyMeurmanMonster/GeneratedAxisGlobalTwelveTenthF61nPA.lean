/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF61nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF61nPO
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthMatF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamFourth

/-! # Pairing parts (octads, matrix, pairs) of the Tenth identification T61- (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem tf61n_hok : octPackOk 32 tf61nL = true :=
  OctadDense.octPackOk_of_chk 32 4 false tf61nL tf61nHC tf61nGC 68352 rfl tf61n_oct

/-- The octad part of the pairing. -/
theorem tf61n_hn : octSumZ 32 false tf61nL tf61nW = 68352 :=
  OctadDense.octSumZ_of_chk 32 4 false tf61nL tf61nW tf61nHC tf61nGC 68352 rfl rfl tf61n_oct

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem tf61n_hm : triMatF false tf61nL tf61nW = ((29 : ℚ) / 8) := by
  rw [triMatF_eq_ZI false tf61nL tf61nW (srcTenthMatZ.act tf61nH) (fourthSrcMatZ.act tf61nG)
    (srcTenthMat_act_entryZ tf61nH) (fourthSrcMat_act_entryZ tf61nG), ← MatZ.actF_eq tf61nH,
    ← MatZ.actF_eq tf61nG]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part of the pairing. -/
theorem tf61n_hp : pairSumQ false tf61nL tf61nW = (2 : ℚ) := by
  rw [pairSumQ_eq_ZI false tf61nL tf61nW (srcTenthMatZ.act tf61nH) (srcTenthMat_act_entryZ tf61nH),
    ← MatZ.actF_eq tf61nH]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
