/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nPAm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nPAp1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nPAp2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nPAp3

/-! # Factory parts (matrix, pairs) of the identification Twelfth[1]- <-> Twelfth[1]+ (record
gtwelfth:W1-, e = -1)

The pair part of the pairing from its two integer sums and the pair self sum. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The pair part equals the pair self part of the target. -/
theorem twGtwelfthW1n_hp : pairSumQ false twGtwelfthW1nL twGtwelfthW1nW = twGtwelfthW1nW.sden *
    (selfPairsZ twGtwelfthW1nW : ℚ) := by
  have hd : (twelfthSrcMatZ.act twGtwelfthW1nH).den = 16 := by decide +kernel
  have hk : (twelfthSrcMatZ.act twGtwelfthW1nH).k = 2 := by decide +kernel
  rw [pairSumQ_eq_ZI false twGtwelfthW1nL twGtwelfthW1nW (twelfthSrcMatZ.act twGtwelfthW1nH)
      (twelfthSrcMat_act_entryZ twGtwelfthW1nH), pairSumZI_eq, twGtwelfthW1n_pm, twGtwelfthW1n_pl,
    twGtwelfthW1n_ps, hd, hk]
  norm_num [twGtwelfthW1nL, twGtwelfthW1nW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
