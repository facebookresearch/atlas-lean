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

/-! # Factory parts (octad check, matrix, pairs) of the identification Fifth[12]- <-> Fourth[2]-
(record gfifth:F12-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGfifthF12n_hok : octPackOk 32 wGfifthF12nL = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGfifthF12n_hm : triMatF false wGfifthF12nL wGfifthF12nW = selfMatQ wGfifthF12nW := by
  rw [triMatF_eq_ZI false wGfifthF12nL wGfifthF12nW (fifthSrcMatZ.act wGfifthF12nH)
      (fourthSrcMatZ.act wGfifthF12nG)
    (fifthSrcMat_act_entry wGfifthF12nH) (fourthSrcMat_act_entryZ wGfifthF12nG),
    selfMatQ_eq_ZI wGfifthF12nW (fourthSrcMatZ.act wGfifthF12nG) (fourthSrcMat_act_entryZ
        wGfifthF12nG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGfifthF12n_hp : pairSumQ false wGfifthF12nL wGfifthF12nW = wGfifthF12nW.sden *
    (selfPairsZ wGfifthF12nW : ℚ) := by
  rw [pairSumQ_eq_ZI false wGfifthF12nL wGfifthF12nW (fifthSrcMatZ.act wGfifthF12nH)
      (fifthSrcMat_act_entry wGfifthF12nH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
