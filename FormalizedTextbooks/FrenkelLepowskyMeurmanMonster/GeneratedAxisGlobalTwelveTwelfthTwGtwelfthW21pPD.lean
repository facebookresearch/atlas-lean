/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pPD1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pPDg0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pPDg1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pPDg2

/-! # Factory parts (odd short terms) of the identification Twelfth[9]+ <-> Twelfth[21]+ (record
gtwelfth:W21+, e = 1)

The odd part of the pairing from its groups and the odd self part of the dense target as a sum
of squares (pairwise distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target list in groups. -/
theorem twGtwelfthW21pGT_groups : twGtwelfthW21pGT = twGtwelfthW21pGTg0 ++ (twGtwelfthW21pGTg1 ++
    (twGtwelfthW21pGTg2)) := by
  simp only [twGtwelfthW21pGT, twGtwelfthW21pGTg0, twGtwelfthW21pGTg1, twGtwelfthW21pGTg2,
      List.append_assoc]

/-- The odd short part equals the odd self part of the target. -/
theorem twGtwelfthW21p_ha : (oddWZ 80 true twGtwelfthW21pHX twGtwelfthW21pW : ℚ) / (2 *
    ((tensorWordDenAll twGtwelfthW21pH : ℚ) * 32)) =
    twGtwelfthW21pW.sden * (selfOddP twGtwelfthW21pW : ℚ) := by
  have hz : oddWZ 80 true twGtwelfthW21pHX twGtwelfthW21pW = 372113408 + (380108800 + (296353792))
      := by
    unfold twGtwelfthW21pW
    rw [oddWZ_ofList, twGtwelfthW21pGT_groups, oddSumF_append, oddSumF_append, twGtwelfthW21p_og0,
        twGtwelfthW21p_og1, twGtwelfthW21p_og2]
  have hd : tensorWordDenAll twGtwelfthW21pH = 4096 := by decide +kernel
  rw [selfOddP_eq, selfOddZ_of_distinct _ twGtwelfthW21p_odist, twGtwelfthW21p_osq, hz, hd]
  norm_num [twGtwelfthW21pW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
