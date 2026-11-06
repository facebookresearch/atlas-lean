/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nPD1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nPDg0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nPDg1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nPDg2

/-! # Factory parts (odd short terms) of the identification Ninth[1]- <-> Tenth[33]+ (record
gninth:N1-, e = -1)

The odd part of the pairing from its groups and the odd self part of the dense target as a sum
of squares (pairwise distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target list in groups. -/
theorem wGninthN1nGT_groups : wGninthN1nGT = wGninthN1nGTg0 ++ (wGninthN1nGTg1 ++
    (wGninthN1nGTg2)) := by
  simp only [wGninthN1nGT, wGninthN1nGTg0, wGninthN1nGTg1, wGninthN1nGTg2, List.append_assoc]

/-- The odd short part equals the odd self part of the target. -/
theorem wGninthN1n_ha : (oddWZ 64 false wGninthN1nHX wGninthN1nW : ℚ) / (2 * ((tensorWordDenAll
    wGninthN1nH : ℚ) * 32)) =
    wGninthN1nW.sden * (selfOddP wGninthN1nW : ℚ) := by
  have hz : oddWZ 64 false wGninthN1nHX wGninthN1nW = 1425408 + (1452416 + (1234560)) := by
    unfold wGninthN1nW
    rw [oddWZ_ofList, wGninthN1nGT_groups, oddSumF_append, oddSumF_append, wGninthN1n_og0,
        wGninthN1n_og1, wGninthN1n_og2]
  have hd : tensorWordDenAll wGninthN1nH = 16 := by decide +kernel
  rw [selfOddP_eq, selfOddZ_of_distinct _ wGninthN1n_odist, wGninthN1n_osq, hz, hd]
  norm_num [wGninthN1nW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
