/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octad check, matrix, pairs) of the identification Ninth[1]+ <-> Twelfth[25]-
(record gninth:N1+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGninthN1pX_hm : triMatF true wGninthN1pXL wGninthN1pXW = selfMatQ wGninthN1pXW := by
  rw [triMatF_eq_ZI true wGninthN1pXL wGninthN1pXW (srcNinthMatZc.act wGninthN1pXH)
      (twelfthSrcMatZ.act wGninthN1pXG)
    (srcNinthMat_act_entryZc wGninthN1pXH) (twelfthSrcMat_act_entryZ wGninthN1pXG),
    selfMatQ_eq_ZI wGninthN1pXW (twelfthSrcMatZ.act wGninthN1pXG) (twelfthSrcMat_act_entryZ
        wGninthN1pXG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGninthN1pX_hp : pairSumQ true wGninthN1pXL wGninthN1pXW = wGninthN1pXW.sden * (selfPairsZ
    wGninthN1pXW : ℚ) := by
  rw [pairSumQ_eq_ZI true wGninthN1pXL wGninthN1pXW (srcNinthMatZc.act wGninthN1pXH)
      (srcNinthMat_act_entryZc wGninthN1pXH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
