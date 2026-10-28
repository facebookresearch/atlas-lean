/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT

/-! # Factory parts (octad check, matrix, pairs) of the identification Eighth[13]- <-> Eighth[13]-
(record goctad:E9-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGoctadE9n_hm : triMatF false wGoctadE9nL wGoctadE9nW = selfMatQ wGoctadE9nW := by
  rw [triMatF_eq_ZI false wGoctadE9nL wGoctadE9nW (eighthSrcMatZ.act wGoctadE9nH)
      (eighthSrcMatZ.act wGoctadE9nG)
    (eighthSrcMat_act_entryZ wGoctadE9nH) (eighthSrcMat_act_entryZ wGoctadE9nG),
    selfMatQ_eq_ZI wGoctadE9nW (eighthSrcMatZ.act wGoctadE9nG) (eighthSrcMat_act_entryZ
        wGoctadE9nG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGoctadE9n_hp : pairSumQ false wGoctadE9nL wGoctadE9nW = wGoctadE9nW.sden * (selfPairsZ
    wGoctadE9nW : ℚ) := by
  rw [pairSumQ_eq_ZI false wGoctadE9nL wGoctadE9nW (eighthSrcMatZ.act wGoctadE9nH)
      (eighthSrcMat_act_entryZ wGoctadE9nH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
