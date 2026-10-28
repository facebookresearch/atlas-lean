/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nPCy
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nPCx
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nPCl0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nPCl1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nPCl2

/-! # Factory parts (tensor) of the identification Root8[12]- <-> Twelfth[34]- (record r8f:R86-, e
= -1)

The tensor part of the pairing from its parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source list in groups. -/
theorem wR8fR86nHT_groups : wR8fR86nHT = wR8fR86nHTg0 ++ (wR8fR86nHTg1 ++ (wR8fR86nHTg2)) := by
  simp only [wR8fR86nHT, wR8fR86nHTg0, wR8fR86nHTg1, wR8fR86nHTg2, List.append_assoc]

/-- The tensor part equals the tensor self part of the target. -/
theorem wR8fR86n_ht : wR8fR86nL.sden * (oddLZ 96 false wR8fR86nGX wR8fR86nL : ℚ) /
    ((tensorWordDenAll wR8fR86nG : ℚ) * 32) + (tdotM 96 (trialityTensorT 96 (!false) wR8fR86nHX)
    wR8fR86nGX : ℚ) / (2 * ((tensorWordDenAll wR8fR86nH : ℚ) * 32) * ((tensorWordDenAll wR8fR86nG
    : ℚ) * 32)) = (tdotM 96 wR8fR86nGX wR8fR86nGX : ℚ) / (((tensorWordDenAll wR8fR86nG : ℚ) * 32)
    * ((tensorWordDenAll wR8fR86nG : ℚ) * 32)) := by
  have hz : oddLZ 96 false wR8fR86nGX wR8fR86nL = 918552576 + (1122369536 + (56229888)) := by
    unfold wR8fR86nL
    rw [oddLZ_ofList, wR8fR86nHT_groups, oddSumL_append, oddSumL_append, wR8fR86n_ol0,
        wR8fR86n_ol1, wR8fR86n_ol2]
  have hd0 : tensorWordDenAll wR8fR86nG = 8192 := by decide +kernel
  have hd1 : tensorWordDenAll wR8fR86nH = 65536 := by decide +kernel
  rw [hz, wR8fR86n_tx, wR8fR86n_ty, hd0, hd1]
  norm_num [wR8fR86nL]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
