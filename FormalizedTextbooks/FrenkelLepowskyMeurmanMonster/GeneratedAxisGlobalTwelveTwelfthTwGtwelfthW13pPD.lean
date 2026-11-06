/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pPD1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pPDg0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pPDg1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pPDg2

/-! # Factory parts (odd short terms) of the identification Twelfth[13]- <-> Twelfth[13]+ (record
gtwelfth:W13+, e = 1)

The odd part of the pairing from its groups and the odd self part of the dense target as a sum
of squares (pairwise distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target list in groups. -/
theorem twGtwelfthW13pGT_groups : twGtwelfthW13pGT = twGtwelfthW13pGTg0 ++ (twGtwelfthW13pGTg1 ++
    (twGtwelfthW13pGTg2)) := by
  simp only [twGtwelfthW13pGT, twGtwelfthW13pGTg0, twGtwelfthW13pGTg1, twGtwelfthW13pGTg2,
      List.append_assoc]

/-- The odd short part equals the odd self part of the target. -/
theorem twGtwelfthW13p_ha : (oddWZ 80 true twGtwelfthW13pHX twGtwelfthW13pW : ℚ) / (2 *
    ((tensorWordDenAll twGtwelfthW13pH : ℚ) * 32)) =
    twGtwelfthW13pW.sden * (selfOddP twGtwelfthW13pW : ℚ) := by
  have hz : oddWZ 80 true twGtwelfthW13pHX twGtwelfthW13pW = 372637696 + (379584512 + (296353792))
      := by
    unfold twGtwelfthW13pW
    rw [oddWZ_ofList, twGtwelfthW13pGT_groups, oddSumF_append, oddSumF_append, twGtwelfthW13p_og0,
        twGtwelfthW13p_og1, twGtwelfthW13p_og2]
  have hd : tensorWordDenAll twGtwelfthW13pH = 4096 := by decide +kernel
  rw [selfOddP_eq, selfOddZ_of_distinct _ twGtwelfthW13p_odist, twGtwelfthW13p_osq, hz, hd]
  norm_num [twGtwelfthW13pW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
