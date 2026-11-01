/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Factory parts (octad check, matrix, pairs) of the identification Eighth[13]+ <->
Seventh[14]+ (record goctad:E9+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGoctadE9p_hm : triMatF true wGoctadE9pL wGoctadE9pW = selfMatQ wGoctadE9pW := by
  rw [triMatF_eq_ZI true wGoctadE9pL wGoctadE9pW (eighthSrcMatZ.act wGoctadE9pH)
      (srcSeventhMatZ.act wGoctadE9pG)
    (eighthSrcMat_act_entryZ wGoctadE9pH) (srcSeventhMat_act_entryZ wGoctadE9pG),
    selfMatQ_eq_ZI wGoctadE9pW (srcSeventhMatZ.act wGoctadE9pG) (srcSeventhMat_act_entryZ
        wGoctadE9pG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGoctadE9p_hp : pairSumQ true wGoctadE9pL wGoctadE9pW = wGoctadE9pW.sden * (selfPairsZ
    wGoctadE9pW : ℚ) := by
  rw [pairSumQ_eq_ZI true wGoctadE9pL wGoctadE9pW (eighthSrcMatZ.act wGoctadE9pH)
      (eighthSrcMat_act_entryZ wGoctadE9pH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
