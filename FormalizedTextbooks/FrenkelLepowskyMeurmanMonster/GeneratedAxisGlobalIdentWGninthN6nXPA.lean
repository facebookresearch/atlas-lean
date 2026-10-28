/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octad check, matrix, pairs) of the identification Ninth[10]- <-> Twelfth[12]-
(record gninth:N6-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGninthN6nX_hm : triMatF false wGninthN6nXL wGninthN6nXW = selfMatQ wGninthN6nXW := by
  rw [triMatF_eq_ZI false wGninthN6nXL wGninthN6nXW (srcNinthMatZc.act wGninthN6nXH)
      (twelfthSrcMatZ.act wGninthN6nXG)
    (srcNinthMat_act_entryZc wGninthN6nXH) (twelfthSrcMat_act_entryZ wGninthN6nXG),
    selfMatQ_eq_ZI wGninthN6nXW (twelfthSrcMatZ.act wGninthN6nXG) (twelfthSrcMat_act_entryZ
        wGninthN6nXG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGninthN6nX_hp : pairSumQ false wGninthN6nXL wGninthN6nXW = wGninthN6nXW.sden *
    (selfPairsZ wGninthN6nXW : ℚ) := by
  rw [pairSumQ_eq_ZI false wGninthN6nXL wGninthN6nXW (srcNinthMatZc.act wGninthN6nXH)
      (srcNinthMat_act_entryZc wGninthN6nXH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
