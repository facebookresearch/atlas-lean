/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c18pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamFourth

/-! # Factory parts (octad check, matrix, pairs) of the identification Fourth[13]- <->
Seventh[27]+ (record gforest:S7c18+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGforestS7c18p_hm : triMatF true wGforestS7c18pL wGforestS7c18pW = selfMatQ
    wGforestS7c18pW := by
  rw [triMatF_eq_ZI true wGforestS7c18pL wGforestS7c18pW (srcSeventhMatZ.act wGforestS7c18pH)
      (fourthSrcMatZ.act wGforestS7c18pG)
    (srcSeventhMat_act_entryZ wGforestS7c18pH) (fourthSrcMat_act_entryZ wGforestS7c18pG),
    selfMatQ_eq_ZI wGforestS7c18pW (fourthSrcMatZ.act wGforestS7c18pG) (fourthSrcMat_act_entryZ
        wGforestS7c18pG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGforestS7c18p_hp : pairSumQ true wGforestS7c18pL wGforestS7c18pW = wGforestS7c18pW.sden *
    (selfPairsZ wGforestS7c18pW : ℚ) := by
  rw [pairSumQ_eq_ZI true wGforestS7c18pL wGforestS7c18pW (srcSeventhMatZ.act wGforestS7c18pH)
      (srcSeventhMat_act_entryZ wGforestS7c18pH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
