/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c14pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT

/-! # Factory parts (octad check, matrix, pairs) of the identification Eighth[27]+ <->
Seventh[22]+ (record gforest:S7c14+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGforestS7c14p_hm : triMatF true wGforestS7c14pL wGforestS7c14pW = selfMatQ
    wGforestS7c14pW := by
  rw [triMatF_eq_ZI true wGforestS7c14pL wGforestS7c14pW (srcSeventhMatZ.act wGforestS7c14pH)
      (eighthSrcMatZ.act wGforestS7c14pG)
    (srcSeventhMat_act_entryZ wGforestS7c14pH) (eighthSrcMat_act_entryZ wGforestS7c14pG),
    selfMatQ_eq_ZI wGforestS7c14pW (eighthSrcMatZ.act wGforestS7c14pG) (eighthSrcMat_act_entryZ
        wGforestS7c14pG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGforestS7c14p_hp : pairSumQ true wGforestS7c14pL wGforestS7c14pW = wGforestS7c14pW.sden *
    (selfPairsZ wGforestS7c14pW : ℚ) := by
  rw [pairSumQ_eq_ZI true wGforestS7c14pL wGforestS7c14pW (srcSeventhMatZ.act wGforestS7c14pH)
      (srcSeventhMat_act_entryZ wGforestS7c14pH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
