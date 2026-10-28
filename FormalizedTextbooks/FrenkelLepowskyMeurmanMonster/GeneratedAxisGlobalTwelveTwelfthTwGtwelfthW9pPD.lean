/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pPD1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pPDg0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pPDg1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pPDg2

/-! # Factory parts (odd short terms) of the identification Twelfth[9]+ <-> Twelfth[21]- (record
gtwelfth:W9+, e = 1)

The odd part of the pairing from its groups and the odd self part of the dense target as a sum
of squares (pairwise distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target list in groups. -/
theorem twGtwelfthW9pGT_groups : twGtwelfthW9pGT = twGtwelfthW9pGTg0 ++ (twGtwelfthW9pGTg1 ++
    (twGtwelfthW9pGTg2)) := by
  simp only [twGtwelfthW9pGT, twGtwelfthW9pGTg0, twGtwelfthW9pGTg1, twGtwelfthW9pGTg2,
      List.append_assoc]

/-- The odd short part equals the odd self part of the target. -/
theorem twGtwelfthW9p_ha : (oddWZ 80 true twGtwelfthW9pHX twGtwelfthW9pW : ℚ) / (2 *
    ((tensorWordDenAll twGtwelfthW9pH : ℚ) * 32)) =
    twGtwelfthW9pW.sden * (selfOddP twGtwelfthW9pW : ℚ) := by
  have hz : oddWZ 80 true twGtwelfthW9pHX twGtwelfthW9pW = 368443392 + (383778816 + (296353792))
      := by
    unfold twGtwelfthW9pW
    rw [oddWZ_ofList, twGtwelfthW9pGT_groups, oddSumF_append, oddSumF_append, twGtwelfthW9p_og0,
        twGtwelfthW9p_og1, twGtwelfthW9p_og2]
  have hd : tensorWordDenAll twGtwelfthW9pH = 4096 := by decide +kernel
  rw [selfOddP_eq, selfOddZ_of_distinct _ twGtwelfthW9p_odist, twGtwelfthW9p_osq, hz, hd]
  norm_num [twGtwelfthW9pW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
