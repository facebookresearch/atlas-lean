/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Factory parts (octad check, matrix, pairs) of the identification Eighth[37]+ <->
Seventh[32]+ (record goctad:E26+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGoctadE26p_hm : triMatF true wGoctadE26pL wGoctadE26pW = selfMatQ wGoctadE26pW := by
  rw [triMatF_eq_ZI true wGoctadE26pL wGoctadE26pW (eighthSrcMatZ.act wGoctadE26pH)
      (srcSeventhMatZ.act wGoctadE26pG)
    (eighthSrcMat_act_entryZ wGoctadE26pH) (srcSeventhMat_act_entryZ wGoctadE26pG),
    selfMatQ_eq_ZI wGoctadE26pW (srcSeventhMatZ.act wGoctadE26pG) (srcSeventhMat_act_entryZ
        wGoctadE26pG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGoctadE26p_hp : pairSumQ true wGoctadE26pL wGoctadE26pW = wGoctadE26pW.sden * (selfPairsZ
    wGoctadE26pW : ℚ) := by
  rw [pairSumQ_eq_ZI true wGoctadE26pL wGoctadE26pW (eighthSrcMatZ.act wGoctadE26pH)
      (eighthSrcMat_act_entryZ wGoctadE26pH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
