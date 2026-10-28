/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pPCy
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pPCx
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pPCl0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pPCl1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pPCl2

/-! # Factory parts (tensor) of the identification Root8[12]+ <-> Twelfth[34]- (record r8f:R86+, e
= 1)

The tensor part of the pairing from its parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source list in groups. -/
theorem wR8fR86pHT_groups : wR8fR86pHT = wR8fR86pHTg0 ++ (wR8fR86pHTg1 ++ (wR8fR86pHTg2)) := by
  simp only [wR8fR86pHT, wR8fR86pHTg0, wR8fR86pHTg1, wR8fR86pHTg2, List.append_assoc]

/-- The tensor part equals the tensor self part of the target. -/
theorem wR8fR86p_ht : wR8fR86pL.sden * (oddLZ 96 true wR8fR86pGX wR8fR86pL : ℚ) /
    ((tensorWordDenAll wR8fR86pG : ℚ) * 32) + (tdotM 96 (trialityTensorT 96 (!true) wR8fR86pHX)
    wR8fR86pGX : ℚ) / (2 * ((tensorWordDenAll wR8fR86pH : ℚ) * 32) * ((tensorWordDenAll wR8fR86pG
    : ℚ) * 32)) = (tdotM 96 wR8fR86pGX wR8fR86pGX : ℚ) / (((tensorWordDenAll wR8fR86pG : ℚ) * 32)
    * ((tensorWordDenAll wR8fR86pG : ℚ) * 32)) := by
  have hz : oddLZ 96 true wR8fR86pGX wR8fR86pL = 918552576 + (1122369536 + (56229888)) := by
    unfold wR8fR86pL
    rw [oddLZ_ofList, wR8fR86pHT_groups, oddSumL_append, oddSumL_append, wR8fR86p_ol0,
        wR8fR86p_ol1, wR8fR86p_ol2]
  have hd0 : tensorWordDenAll wR8fR86pG = 8192 := by decide +kernel
  have hd1 : tensorWordDenAll wR8fR86pH = 65536 := by decide +kernel
  rw [hz, wR8fR86p_tx, wR8fR86p_ty, hd0, hd1]
  norm_num [wR8fR86pL]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
