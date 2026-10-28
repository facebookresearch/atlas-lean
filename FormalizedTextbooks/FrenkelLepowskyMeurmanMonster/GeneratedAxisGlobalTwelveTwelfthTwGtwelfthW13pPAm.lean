/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (matrix) of the identification Twelfth[13]- <-> Twelfth[13]+ (record
gtwelfth:W13+, e = 1)

Dense pair blocks: the pair part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false


set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem twGtwelfthW13p_hm : triMatF true twGtwelfthW13pL twGtwelfthW13pW = selfMatQ
    twGtwelfthW13pW := by
  rw [triMatF_eq_ZI true twGtwelfthW13pL twGtwelfthW13pW (twelfthSrcMatZ.act twGtwelfthW13pH)
      (twelfthSrcMatZ.act twGtwelfthW13pG)
    (twelfthSrcMat_act_entryZ twGtwelfthW13pH) (twelfthSrcMat_act_entryZ twGtwelfthW13pG),
    selfMatQ_eq_ZI twGtwelfthW13pW (twelfthSrcMatZ.act twGtwelfthW13pG) (twelfthSrcMat_act_entryZ
        twGtwelfthW13pG)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
