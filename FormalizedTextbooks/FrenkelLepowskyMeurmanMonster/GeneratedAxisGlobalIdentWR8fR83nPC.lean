/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nPCy
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nPCx
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nPCl0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nPCl1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nPCl2

/-! # Factory parts (tensor) of the identification Root8[11]- <-> Twelfth[29]- (record r8f:R83-, e
= -1)

The tensor part of the pairing from its parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source list in groups. -/
theorem wR8fR83nHT_groups : wR8fR83nHT = wR8fR83nHTg0 ++ (wR8fR83nHTg1 ++ (wR8fR83nHTg2)) := by
  simp only [wR8fR83nHT, wR8fR83nHTg0, wR8fR83nHTg1, wR8fR83nHTg2, List.append_assoc]

/-- The tensor part equals the tensor self part of the target. -/
theorem wR8fR83n_ht : wR8fR83nL.sden * (oddLZ 72 false wR8fR83nGX wR8fR83nL : ℚ) /
    ((tensorWordDenAll wR8fR83nG : ℚ) * 32) + (tdotM 72 (trialityTensorT 72 (!false) wR8fR83nHX)
    wR8fR83nGX : ℚ) / (2 * ((tensorWordDenAll wR8fR83nH : ℚ) * 32) * ((tensorWordDenAll wR8fR83nG
    : ℚ) * 32)) = (tdotM 72 wR8fR83nGX wR8fR83nGX : ℚ) / (((tensorWordDenAll wR8fR83nG : ℚ) * 32)
    * ((tensorWordDenAll wR8fR83nG : ℚ) * 32)) := by
  have hz : oddLZ 72 false wR8fR83nGX wR8fR83nL = 122945536 + (133791744 + (6455296)) := by
    unfold wR8fR83nL
    rw [oddLZ_ofList, wR8fR83nHT_groups, oddSumL_append, oddSumL_append, wR8fR83n_ol0,
        wR8fR83n_ol1, wR8fR83n_ol2]
  have hd0 : tensorWordDenAll wR8fR83nG = 1024 := by decide +kernel
  have hd1 : tensorWordDenAll wR8fR83nH = 256 := by decide +kernel
  rw [hz, wR8fR83n_tx, wR8fR83n_ty, hd0, hd1]
  norm_num [wR8fR83nL]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
