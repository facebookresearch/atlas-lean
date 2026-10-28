/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nPD1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nPDg0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nPDg1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nPDg2

/-! # Factory parts (odd short terms) of the identification Twelfth[1]- <-> Twelfth[1]+ (record
gtwelfth:W1-, e = -1)

The odd part of the pairing from its groups and the odd self part of the dense target as a sum
of squares (pairwise distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target list in groups. -/
theorem twGtwelfthW1nGT_groups : twGtwelfthW1nGT = twGtwelfthW1nGTg0 ++ (twGtwelfthW1nGTg1 ++
    (twGtwelfthW1nGTg2)) := by
  simp only [twGtwelfthW1nGT, twGtwelfthW1nGTg0, twGtwelfthW1nGTg1, twGtwelfthW1nGTg2,
      List.append_assoc]

/-- The odd short part equals the odd self part of the target. -/
theorem twGtwelfthW1n_ha : (oddWZ 64 false twGtwelfthW1nHX twGtwelfthW1nW : ℚ) / (2 *
    ((tensorWordDenAll twGtwelfthW1nH : ℚ) * 32)) =
    twGtwelfthW1nW.sden * (selfOddP twGtwelfthW1nW : ℚ) := by
  have hz : oddWZ 64 false twGtwelfthW1nHX twGtwelfthW1nW = 23199744 + (23814144 + (18522112)) := by
    unfold twGtwelfthW1nW
    rw [oddWZ_ofList, twGtwelfthW1nGT_groups, oddSumF_append, oddSumF_append, twGtwelfthW1n_og0,
        twGtwelfthW1n_og1, twGtwelfthW1n_og2]
  have hd : tensorWordDenAll twGtwelfthW1nH = 256 := by decide +kernel
  rw [selfOddP_eq, selfOddZ_of_distinct _ twGtwelfthW1n_odist, twGtwelfthW1n_osq, hz, hd]
  norm_num [twGtwelfthW1nW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
