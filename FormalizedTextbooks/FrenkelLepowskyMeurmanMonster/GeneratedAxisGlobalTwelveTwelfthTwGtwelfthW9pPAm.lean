/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (matrix) of the identification Twelfth[9]+ <-> Twelfth[21]- (record
gtwelfth:W9+, e = 1)

Dense pair blocks: the pair part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false


set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem twGtwelfthW9p_hm : triMatF true twGtwelfthW9pL twGtwelfthW9pW = selfMatQ twGtwelfthW9pW :=
    by
  rw [triMatF_eq_ZI true twGtwelfthW9pL twGtwelfthW9pW (twelfthSrcMatZ.act twGtwelfthW9pH)
      (twelfthSrcMatZ.act twGtwelfthW9pG)
    (twelfthSrcMat_act_entryZ twGtwelfthW9pH) (twelfthSrcMat_act_entryZ twGtwelfthW9pG),
    selfMatQ_eq_ZI twGtwelfthW9pW (twelfthSrcMatZ.act twGtwelfthW9pG) (twelfthSrcMat_act_entryZ
        twGtwelfthW9pG)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
