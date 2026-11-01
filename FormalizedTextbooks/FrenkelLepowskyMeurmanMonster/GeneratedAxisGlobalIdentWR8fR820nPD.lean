/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820nPD1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820nPDg0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820nPDg1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820nPDg2

/-! # Factory parts (odd short terms) of the identification Root8[25]- <-> Root8[25]- (record
r8f:R820-, e = -1)

The odd part of the pairing from its groups and the odd self part of the dense target as a sum
of squares (pairwise distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target list in groups. -/
theorem wR8fR820nGT_groups : wR8fR820nGT = wR8fR820nGTg0 ++ (wR8fR820nGTg1 ++ (wR8fR820nGTg2)) := by
  simp only [wR8fR820nGT, wR8fR820nGTg0, wR8fR820nGTg1, wR8fR820nGTg2, List.append_assoc]

/-- The odd short part equals the odd self part of the target. -/
theorem wR8fR820n_ha : (oddWZ 64 false wR8fR820nHX wR8fR820nW : ℚ) / (2 * ((tensorWordDenAll
    wR8fR820nH : ℚ) * 32)) =
    wR8fR820nW.sden * (selfOddP wR8fR820nW : ℚ) := by
  have hz : oddWZ 64 false wR8fR820nHX wR8fR820nW = 1654784 + (1966080 + (49152)) := by
    unfold wR8fR820nW
    rw [oddWZ_ofList, wR8fR820nGT_groups, oddSumF_append, oddSumF_append, wR8fR820n_og0,
        wR8fR820n_og1, wR8fR820n_og2]
  have hd : tensorWordDenAll wR8fR820nH = 16 := by decide +kernel
  rw [selfOddP_eq, selfOddZ_of_distinct _ wR8fR820n_odist, wR8fR820n_osq, hz, hd]
  norm_num [wR8fR820nW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
