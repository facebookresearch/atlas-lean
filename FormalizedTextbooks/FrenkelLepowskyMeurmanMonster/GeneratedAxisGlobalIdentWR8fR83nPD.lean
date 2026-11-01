/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nPD1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nPDg0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nPDg1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nPDg2

/-! # Factory parts (odd short terms) of the identification Root8[11]- <-> Twelfth[29]- (record
r8f:R83-, e = -1)

The odd part of the pairing from its groups and the odd self part of the dense target as a sum
of squares (pairwise distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target list in groups. -/
theorem wR8fR83nGT_groups : wR8fR83nGT = wR8fR83nGTg0 ++ (wR8fR83nGTg1 ++ (wR8fR83nGTg2)) := by
  simp only [wR8fR83nGT, wR8fR83nGTg0, wR8fR83nGTg1, wR8fR83nGTg2, List.append_assoc]

/-- The odd short part equals the odd self part of the target. -/
theorem wR8fR83n_ha : (oddWZ 72 false wR8fR83nHX wR8fR83nW : ℚ) / (2 * ((tensorWordDenAll
    wR8fR83nH : ℚ) * 32)) =
    wR8fR83nW.sden * (selfOddP wR8fR83nW : ℚ) := by
  have hz : oddWZ 72 false wR8fR83nHX wR8fR83nW = 20013056 + (25608192 + (20176896)) := by
    unfold wR8fR83nW
    rw [oddWZ_ofList, wR8fR83nGT_groups, oddSumF_append, oddSumF_append, wR8fR83n_og0,
        wR8fR83n_og1, wR8fR83n_og2]
  have hd : tensorWordDenAll wR8fR83nH = 256 := by decide +kernel
  rw [selfOddP_eq, selfOddZ_of_distinct _ wR8fR83n_odist, wR8fR83n_osq, hz, hd]
  norm_num [wR8fR83nW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
