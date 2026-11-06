/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pPAm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pPAp1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pPAp2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pPAp3

/-! # Factory parts (matrix, pairs) of the identification Twelfth[9]+ <-> Twelfth[21]+ (record
gtwelfth:W21+, e = 1)

The pair part of the pairing from its two integer sums and the pair self sum. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The pair part equals the pair self part of the target. -/
theorem twGtwelfthW21p_hp : pairSumQ true twGtwelfthW21pL twGtwelfthW21pW = twGtwelfthW21pW.sden *
    (selfPairsZ twGtwelfthW21pW : ℚ) := by
  have hd : (twelfthSrcMatZ.act twGtwelfthW21pH).den = 16 := by decide +kernel
  have hk : (twelfthSrcMatZ.act twGtwelfthW21pH).k = 3 := by decide +kernel
  rw [pairSumQ_eq_ZI true twGtwelfthW21pL twGtwelfthW21pW (twelfthSrcMatZ.act twGtwelfthW21pH)
      (twelfthSrcMat_act_entryZ twGtwelfthW21pH), pairSumZI_eq, twGtwelfthW21p_pm,
      twGtwelfthW21p_pl,
    twGtwelfthW21p_ps, hd, hk]
  norm_num [twGtwelfthW21pL, twGtwelfthW21pW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
