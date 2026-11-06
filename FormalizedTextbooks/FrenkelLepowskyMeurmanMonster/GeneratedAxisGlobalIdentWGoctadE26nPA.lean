/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Factory parts (octad check, matrix, pairs) of the identification Eighth[37]- <-> Seventh[1]+
(record goctad:E26-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGoctadE26n_hm : triMatF false wGoctadE26nL wGoctadE26nW = selfMatQ wGoctadE26nW := by
  rw [triMatF_eq_ZI false wGoctadE26nL wGoctadE26nW (eighthSrcMatZ.act wGoctadE26nH)
      (srcSeventhMatZ.act wGoctadE26nG)
    (eighthSrcMat_act_entryZ wGoctadE26nH) (srcSeventhMat_act_entryZ wGoctadE26nG),
    selfMatQ_eq_ZI wGoctadE26nW (srcSeventhMatZ.act wGoctadE26nG) (srcSeventhMat_act_entryZ
        wGoctadE26nG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGoctadE26n_hp : pairSumQ false wGoctadE26nL wGoctadE26nW = wGoctadE26nW.sden *
    (selfPairsZ wGoctadE26nW : ℚ) := by
  rw [pairSumQ_eq_ZI false wGoctadE26nL wGoctadE26nW (eighthSrcMatZ.act wGoctadE26nH)
      (eighthSrcMat_act_entryZ wGoctadE26nH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
