/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pPAm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pPAp
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pPAp3

/-! # Factory parts (matrix, pairs) of the identification Twelfth[9]+ <-> Twelfth[21]- (record
gtwelfth:W9+, e = 1)

The pair part of the pairing from its two integer sums and the pair self sum. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The pair part equals the pair self part of the target. -/
theorem twGtwelfthW9p_hp : pairSumQ true twGtwelfthW9pL twGtwelfthW9pW = twGtwelfthW9pW.sden *
    (selfPairsZ twGtwelfthW9pW : ℚ) := by
  rw [pairSumQ_of_chk true twGtwelfthW9pL twGtwelfthW9pW (twelfthSrcMatZ.act twGtwelfthW9pH)
      (twelfthSrcMat_act_entryZ twGtwelfthW9pH) twGtwelfthW9p_pchk, twGtwelfthW9p_ps]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
