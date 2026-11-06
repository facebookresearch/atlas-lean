/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (matrix) of the identification Twelfth[36]+ <-> Twelfth[36]+ (record
gtwelfth:W36+, e = 1)

Dense pair blocks: the pair part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false


set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem twGtwelfthW36p_hm : triMatF true twGtwelfthW36pL twGtwelfthW36pW = selfMatQ
    twGtwelfthW36pW := by
  rw [triMatF_eq_ZI true twGtwelfthW36pL twGtwelfthW36pW (twelfthSrcMatZ.act twGtwelfthW36pH)
      (twelfthSrcMatZ.act twGtwelfthW36pG)
    (twelfthSrcMat_act_entryZ twGtwelfthW36pH) (twelfthSrcMat_act_entryZ twGtwelfthW36pG),
    selfMatQ_eq_ZI twGtwelfthW36pW (twelfthSrcMatZ.act twGtwelfthW36pG) (twelfthSrcMat_act_entryZ
        twGtwelfthW36pG)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
