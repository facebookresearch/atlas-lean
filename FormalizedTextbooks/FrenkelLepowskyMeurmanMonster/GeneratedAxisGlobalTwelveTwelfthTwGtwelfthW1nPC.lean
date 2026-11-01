/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nPCy
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nPCx
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nPCl0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nPCl1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nPCl2

/-! # Factory parts (tensor) of the identification Twelfth[1]- <-> Twelfth[1]+ (record
gtwelfth:W1-, e = -1)

The tensor part of the pairing from its parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source list in groups. -/
theorem twGtwelfthW1nHT_groups : twGtwelfthW1nHT = twGtwelfthW1nHTg0 ++ (twGtwelfthW1nHTg1 ++
    (twGtwelfthW1nHTg2)) := by
  simp only [twGtwelfthW1nHT, twGtwelfthW1nHTg0, twGtwelfthW1nHTg1, twGtwelfthW1nHTg2,
      List.append_assoc]

/-- The tensor part equals the tensor self part of the target. -/
theorem twGtwelfthW1n_ht : twGtwelfthW1nL.sden * (oddLZ 64 false twGtwelfthW1nGX twGtwelfthW1nL :
    ℚ) / ((tensorWordDenAll twGtwelfthW1nG : ℚ) * 32) + (tdotM 64 (trialityTensorT 64 (!false)
    twGtwelfthW1nHX) twGtwelfthW1nGX : ℚ) / (2 * ((tensorWordDenAll twGtwelfthW1nH : ℚ) * 32) *
    ((tensorWordDenAll twGtwelfthW1nG : ℚ) * 32)) = (tdotM 64 twGtwelfthW1nGX twGtwelfthW1nGX : ℚ)
    / (((tensorWordDenAll twGtwelfthW1nG : ℚ) * 32) * ((tensorWordDenAll twGtwelfthW1nG : ℚ) *
    32)) := by
  have hz : oddLZ 64 false twGtwelfthW1nGX twGtwelfthW1nL = 46399488 + (47628288 + (37044224)) := by
    unfold twGtwelfthW1nL
    rw [oddLZ_ofList, twGtwelfthW1nHT_groups, oddSumL_append, oddSumL_append, twGtwelfthW1n_ol0,
        twGtwelfthW1n_ol1, twGtwelfthW1n_ol2]
  have hd0 : tensorWordDenAll twGtwelfthW1nG = 512 := by decide +kernel
  have hd1 : tensorWordDenAll twGtwelfthW1nH = 256 := by decide +kernel
  rw [hz, twGtwelfthW1n_tx, twGtwelfthW1n_ty, hd0, hd1]
  norm_num [twGtwelfthW1nL]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
