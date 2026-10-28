/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR817pPD1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR817pPDg0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR817pPDg1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR817pPDg2

/-! # Factory parts (odd short terms) of the identification Root8[26]+ <-> Root8[26]+ (record
r8f:R817+, e = 1)

The odd part of the pairing from its groups and the odd self part of the dense target as a sum
of squares (pairwise distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target list in groups. -/
theorem wR8fR817pGT_groups : wR8fR817pGT = wR8fR817pGTg0 ++ (wR8fR817pGTg1 ++ (wR8fR817pGTg2)) := by
  simp only [wR8fR817pGT, wR8fR817pGTg0, wR8fR817pGTg1, wR8fR817pGTg2, List.append_assoc]

/-- The odd short part equals the odd self part of the target. -/
theorem wR8fR817p_ha : (oddWZ 64 true wR8fR817pHX wR8fR817pW : ℚ) / (2 * ((tensorWordDenAll
    wR8fR817pH : ℚ) * 32)) =
    wR8fR817pW.sden * (selfOddP wR8fR817pW : ℚ) := by
  have hz : oddWZ 64 true wR8fR817pHX wR8fR817pW = 28835840 + (33245184 + (1619968)) := by
    unfold wR8fR817pW
    rw [oddWZ_ofList, wR8fR817pGT_groups, oddSumF_append, oddSumF_append, wR8fR817p_og0,
        wR8fR817p_og1, wR8fR817p_og2]
  have hd : tensorWordDenAll wR8fR817pH = 256 := by decide +kernel
  rw [selfOddP_eq, selfOddZ_of_distinct _ wR8fR817p_odist, wR8fR817p_osq, hz, hd]
  norm_num [wR8fR817pW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
