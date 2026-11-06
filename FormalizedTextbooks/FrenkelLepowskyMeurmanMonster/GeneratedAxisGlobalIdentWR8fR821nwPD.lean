/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nwPD1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nwPDg0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nwPDg1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nwPDg2

/-! # Factory parts (odd short terms) of the identification Root8[33]- <-> Root8[33]- (record
r8f:R821-, e = -1)

The odd part of the pairing from its groups and the odd self part of the dense target as a sum
of squares (pairwise distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target list in groups. -/
theorem wR8fR821nwGT_groups : wR8fR821nwGT = wR8fR821nwGTg0 ++ (wR8fR821nwGTg1 ++
    (wR8fR821nwGTg2)) := by
  simp only [wR8fR821nwGT, wR8fR821nwGTg0, wR8fR821nwGTg1, wR8fR821nwGTg2, List.append_assoc]

/-- The odd short part equals the odd self part of the target. -/
theorem wR8fR821nw_ha : (oddWZ 96 false wR8fR821nwHX wR8fR821nwW : ℚ) / (2 * ((tensorWordDenAll
    wR8fR821nwH : ℚ) * 32)) =
    wR8fR821nwW.sden * (selfOddP wR8fR821nwW : ℚ) := by
  have hz : oddWZ 96 false wR8fR821nwHX wR8fR821nwW = 914358272 + (1061814272 + (62259200)) := by
    unfold wR8fR821nwW
    rw [oddWZ_ofList, wR8fR821nwGT_groups, oddSumF_append, oddSumF_append, wR8fR821nw_og0,
        wR8fR821nw_og1, wR8fR821nw_og2]
  have hd : tensorWordDenAll wR8fR821nwH = 8192 := by decide +kernel
  rw [selfOddP_eq, selfOddZ_of_distinct _ wR8fR821nw_odist, wR8fR821nw_osq, hz, hd]
  norm_num [wR8fR821nwW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
