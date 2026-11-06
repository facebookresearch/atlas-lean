/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pPD1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pPDg0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pPDg1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pPDg2

/-! # Factory parts (odd short terms) of the identification Twelfth[36]+ <-> Twelfth[36]+ (record
gtwelfth:W36+, e = 1)

The odd part of the pairing from its groups and the odd self part of the dense target as a sum
of squares (pairwise distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target list in groups. -/
theorem twGtwelfthW36pGT_groups : twGtwelfthW36pGT = twGtwelfthW36pGTg0 ++ (twGtwelfthW36pGTg1 ++
    (twGtwelfthW36pGTg2)) := by
  simp only [twGtwelfthW36pGT, twGtwelfthW36pGTg0, twGtwelfthW36pGTg1, twGtwelfthW36pGTg2,
      List.append_assoc]

/-- The odd short part equals the odd self part of the target. -/
theorem twGtwelfthW36p_ha : (oddWZ 64 true twGtwelfthW36pHX twGtwelfthW36pW : ℚ) / (2 *
    ((tensorWordDenAll twGtwelfthW36pH : ℚ) * 32)) =
    twGtwelfthW36pW.sden * (selfOddP twGtwelfthW36pW : ℚ) := by
  have hz : oddWZ 64 true twGtwelfthW36pHX twGtwelfthW36pW = 23904256 + (24682496 + (18522112)) :=
      by
    unfold twGtwelfthW36pW
    rw [oddWZ_ofList, twGtwelfthW36pGT_groups, oddSumF_append, oddSumF_append, twGtwelfthW36p_og0,
        twGtwelfthW36p_og1, twGtwelfthW36p_og2]
  have hd : tensorWordDenAll twGtwelfthW36pH = 256 := by decide +kernel
  rw [selfOddP_eq, selfOddZ_of_distinct _ twGtwelfthW36p_odist, twGtwelfthW36p_osq, hz, hd]
  norm_num [twGtwelfthW36pW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
