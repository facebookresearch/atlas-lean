/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (matrix) of the identification Twelfth[1]- <-> Twelfth[1]+ (record
gtwelfth:W1-, e = -1)

Dense pair blocks: the pair part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false


set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem twGtwelfthW1n_hm : triMatF false twGtwelfthW1nL twGtwelfthW1nW = selfMatQ twGtwelfthW1nW
    := by
  rw [triMatF_eq_ZI false twGtwelfthW1nL twGtwelfthW1nW (twelfthSrcMatZ.act twGtwelfthW1nH)
      (twelfthSrcMatZ.act twGtwelfthW1nG)
    (twelfthSrcMat_act_entryZ twGtwelfthW1nH) (twelfthSrcMat_act_entryZ twGtwelfthW1nG),
    selfMatQ_eq_ZI twGtwelfthW1nW (twelfthSrcMatZ.act twGtwelfthW1nG) (twelfthSrcMat_act_entryZ
        twGtwelfthW1nG)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
