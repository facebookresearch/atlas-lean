/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nPCy
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nPCx
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nPCl0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nPCl1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nPCl2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nPCl3

/-! # Factory parts (tensor) of the identification Ninth[1]- <-> Tenth[33]+ (record gninth:N1-, e
= -1)

The tensor part of the pairing from its parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source list in groups. -/
theorem wGninthN1nHT_groups : wGninthN1nHT = wGninthN1nHTg0 ++ (wGninthN1nHTg1 ++
    (wGninthN1nHTg2 ++ (wGninthN1nHTg3))) := by
  simp only [wGninthN1nHT, wGninthN1nHTg0, wGninthN1nHTg1, wGninthN1nHTg2, wGninthN1nHTg3,
      List.append_assoc]

/-- The tensor part equals the tensor self part of the target. -/
theorem wGninthN1n_ht : wGninthN1nL.sden * (oddLZ 64 false wGninthN1nGX wGninthN1nL : ℚ) /
    ((tensorWordDenAll wGninthN1nG : ℚ) * 32) + (tdotM 64 (trialityTensorT 64 (!false)
    wGninthN1nHX) wGninthN1nGX : ℚ) / (2 * ((tensorWordDenAll wGninthN1nH : ℚ) * 32) *
    ((tensorWordDenAll wGninthN1nG : ℚ) * 32)) = (tdotM 64 wGninthN1nGX wGninthN1nGX : ℚ) /
    (((tensorWordDenAll wGninthN1nG : ℚ) * 32) * ((tensorWordDenAll wGninthN1nG : ℚ) * 32)) := by
  have hz : oddLZ 64 false wGninthN1nGX wGninthN1nL = 23166976 + (44466176 + (37289984 +
      (25624576))) := by
    unfold wGninthN1nL
    rw [oddLZ_ofList, wGninthN1nHT_groups, oddSumL_append, oddSumL_append, oddSumL_append,
        wGninthN1n_ol0, wGninthN1n_ol1, wGninthN1n_ol2, wGninthN1n_ol3]
  have hd0 : tensorWordDenAll wGninthN1nG = 512 := by decide +kernel
  have hd1 : tensorWordDenAll wGninthN1nH = 16 := by decide +kernel
  rw [hz, wGninthN1n_tx, wGninthN1n_ty, hd0, hd1]
  norm_num [wGninthN1nL]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
