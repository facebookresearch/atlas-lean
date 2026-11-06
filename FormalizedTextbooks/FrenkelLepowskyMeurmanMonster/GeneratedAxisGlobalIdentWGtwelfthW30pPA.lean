/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGtwelfthW30pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octad check, matrix, pairs) of the identification Twelfth[30]- <->
Twelfth[30]+ (record gtwelfth:W30+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGtwelfthW30p_hm : triMatF true wGtwelfthW30pL wGtwelfthW30pW = selfMatQ wGtwelfthW30pW :=
    by
  rw [triMatF_eq_ZI true wGtwelfthW30pL wGtwelfthW30pW (twelfthSrcMatZ.act wGtwelfthW30pH)
      (twelfthSrcMatZ.act wGtwelfthW30pG)
    (twelfthSrcMat_act_entryZ wGtwelfthW30pH) (twelfthSrcMat_act_entryZ wGtwelfthW30pG),
    selfMatQ_eq_ZI wGtwelfthW30pW (twelfthSrcMatZ.act wGtwelfthW30pG) (twelfthSrcMat_act_entryZ
        wGtwelfthW30pG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGtwelfthW30p_hp : pairSumQ true wGtwelfthW30pL wGtwelfthW30pW = wGtwelfthW30pW.sden *
    (selfPairsZ wGtwelfthW30pW : ℚ) := by
  rw [pairSumQ_eq_ZI true wGtwelfthW30pL wGtwelfthW30pW (twelfthSrcMatZ.act wGtwelfthW30pH)
      (twelfthSrcMat_act_entryZ wGtwelfthW30pH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
