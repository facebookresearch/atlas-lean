/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pPAm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pPAp
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pPAp3

/-! # Factory parts (matrix, pairs) of the identification Twelfth[36]+ <-> Twelfth[36]+ (record
gtwelfth:W36+, e = 1)

The pair part of the pairing from its two integer sums and the pair self sum. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The pair part equals the pair self part of the target. -/
theorem twGtwelfthW36p_hp : pairSumQ true twGtwelfthW36pL twGtwelfthW36pW = twGtwelfthW36pW.sden *
    (selfPairsZ twGtwelfthW36pW : ℚ) := by
  rw [pairSumQ_of_chk true twGtwelfthW36pL twGtwelfthW36pW (twelfthSrcMatZ.act twGtwelfthW36pH)
      (twelfthSrcMat_act_entryZ twGtwelfthW36pH) twGtwelfthW36p_pchk, twGtwelfthW36p_ps]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
