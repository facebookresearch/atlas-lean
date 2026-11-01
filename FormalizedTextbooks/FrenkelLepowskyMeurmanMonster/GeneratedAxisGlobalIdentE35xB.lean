/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE35H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE35xW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFamX64Root8
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification E35- (Root8 target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = false`) of `e35VH` (Eighth coset image) with `e35xVW` (Root8 image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e35x_EH : e35EH = 33554432 := by
  unfold e35EH
  rw [show tensorWordDenAll e35H = 4096 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e35x_EW : e35xEW = 4194304 := by
  unfold e35xEW
  rw [show tensorWordDenAll e35xW = 131072 by decide]
  norm_num

/-- The packed tensor of the target image over the width-64 literal source tensor. -/
def e35xXWL : List SVec := tensorPlanS 64 e35xPlanW r8X64

/-- The two descriptions of the target tensor agree. -/
theorem e35xXW_eqL : e35xXW = e35xXWL := by
  unfold e35xXW e35xXWL
  rw [r8X64_eq]

/-- The tensor bound of the literal description. -/
theorem e35xXWL_bnd : TBnd 64 (34359738368 * 15) e35xXWL := by
  rw [← e35xXW_eqL]
  exact e35xXW_bnd

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the source tensor. -/
theorem e35x_oddChkAh : OddDense.oddChk 64 (16777216 * 10496 / 2 ^ 16) false true e35xTW
    (TSplit.thi 64 16 e35XH) (4030464 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the source tensor. -/
theorem e35x_oddChkAl : OddDense.oddChk 64 (2 ^ 16 - 1) false true e35xTW
    (TSplit.tlo 64 16 e35XH) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e35x_partA : oddWZ 64 false e35XH e35xVW = (264140488704 : ℤ) := by
  rw [TSplit.oddWZ_split 64 16 (by norm_num) false e35XH e35xVW,
    TSplit.oddWZ_of_chk2 false e35xVW e35xTW e35xVW_sh (TSplit.thi_bnd (by norm_num) e35XH_bnd) e35x_oddChkAh,
    TSplit.oddWZ_of_chk2 false e35xVW e35xTW e35xVW_sh (TSplit.tlo_bnd 64 16 (by norm_num) e35XH) e35x_oddChkAl]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e35x_oddChkBh : OddDense.oddChk 64 (34359738368 * 15 / 2 ^ 16) true false e35TH
    (TSplit.thi 64 16 e35xXWL) (128000 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e35x_oddChkBl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e35TH
    (TSplit.tlo 64 16 e35xXWL) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e35x_partB : oddLZ 64 false e35xXW e35VH = (8388608000 : ℤ) := by
  rw [e35xXW_eqL, TSplit.oddLZ_split 64 16 (by norm_num) false e35xXWL e35VH,
    TSplit.oddLZ_of_chk2 false e35VH e35TH e35VH_sh (TSplit.thi_bnd (by norm_num) e35xXWL_bnd) e35x_oddChkBh,
    TSplit.oddLZ_of_chk2 false e35VH e35TH e35VH_sh (TSplit.tlo_bnd 64 16 (by norm_num) e35xXWL) e35x_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e35x_tchk : TSplit.tdotSplitChk 64 16 (4 * (16777216 * 10496)) (34359738368 * 15)
    (trialityTensorT 64 true e35XH) e35xXWL (17592186044416000 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e35x_partC : tdot 64 (trialityTensorT 64 true e35XH) e35xXW = (17592186044416000 : ℤ) := by
  rw [e35xXW_eqL, TSplit.tdot_of_splitChk (trialityTensorT_spec true e35XH_bnd (by norm_num)).1 e35xXWL_bnd e35x_tchk]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
