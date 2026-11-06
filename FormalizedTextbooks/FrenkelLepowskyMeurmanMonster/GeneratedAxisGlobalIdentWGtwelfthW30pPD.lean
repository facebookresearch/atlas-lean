/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGtwelfthW30pPD1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGtwelfthW30pPDg0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGtwelfthW30pPDg1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGtwelfthW30pPDg2

/-! # Factory parts (odd short terms) of the identification Twelfth[30]- <-> Twelfth[30]+ (record
gtwelfth:W30+, e = 1)

The odd part of the pairing from its groups and the odd self part of the dense target as a sum
of squares (pairwise distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target list in groups. -/
theorem wGtwelfthW30pGT_groups : wGtwelfthW30pGT = wGtwelfthW30pGTg0 ++ (wGtwelfthW30pGTg1 ++
    (wGtwelfthW30pGTg2)) := by
  simp only [wGtwelfthW30pGT, wGtwelfthW30pGTg0, wGtwelfthW30pGTg1, wGtwelfthW30pGTg2,
      List.append_assoc]

/-- The odd short part equals the odd self part of the target. -/
theorem wGtwelfthW30p_ha : (oddWZ 64 true wGtwelfthW30pHX wGtwelfthW30pW : ℚ) / (2 *
    ((tensorWordDenAll wGtwelfthW30pH : ℚ) * 32)) =
    wGtwelfthW30pW.sden * (selfOddP wGtwelfthW30pW : ℚ) := by
  have hz : oddWZ 64 true wGtwelfthW30pHX wGtwelfthW30pW = 22724608 + (24289280 + (18522112)) := by
    unfold wGtwelfthW30pW
    rw [oddWZ_ofList, wGtwelfthW30pGT_groups, oddSumF_append, oddSumF_append, wGtwelfthW30p_og0,
        wGtwelfthW30p_og1, wGtwelfthW30p_og2]
  have hd : tensorWordDenAll wGtwelfthW30pH = 256 := by decide +kernel
  rw [selfOddP_eq, selfOddZ_of_distinct _ wGtwelfthW30p_odist, wGtwelfthW30p_osq, hz, hd]
  norm_num [wGtwelfthW30pW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
