/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pPAm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pPAp
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pPAp3

/-! # Factory parts (matrix, pairs) of the identification Twelfth[13]- <-> Twelfth[13]+ (record
gtwelfth:W13+, e = 1)

The pair part of the pairing from its two integer sums and the pair self sum. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The pair part equals the pair self part of the target. -/
theorem twGtwelfthW13p_hp : pairSumQ true twGtwelfthW13pL twGtwelfthW13pW = twGtwelfthW13pW.sden *
    (selfPairsZ twGtwelfthW13pW : ℚ) := by
  rw [pairSumQ_of_chk true twGtwelfthW13pL twGtwelfthW13pW (twelfthSrcMatZ.act twGtwelfthW13pH)
      (twelfthSrcMat_act_entryZ twGtwelfthW13pH) twGtwelfthW13p_pchk, twGtwelfthW13p_ps]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
