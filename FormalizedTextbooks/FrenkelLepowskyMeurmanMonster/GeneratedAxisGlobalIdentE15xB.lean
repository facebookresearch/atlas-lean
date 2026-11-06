/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE15H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE15xW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFamX64Root8
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification E15+ (Root8 target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = true`) of `e15VH` (Eighth coset image) with `e15xVW` (Root8 image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e15x_EH : e15EH = 33554432 := by
  unfold e15EH
  rw [show tensorWordDenAll e15H = 4096 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e15x_EW : e15xEW = 8388608 := by
  unfold e15xEW
  rw [show tensorWordDenAll e15xW = 262144 by decide]
  norm_num

/-- The packed tensor of the target image over the width-64 literal source tensor. -/
def e15xXWL : List SVec := tensorPlanS 64 e15xPlanW r8X64

/-- The two descriptions of the target tensor agree. -/
theorem e15xXW_eqL : e15xXW = e15xXWL := by
  unfold e15xXW e15xXWL
  rw [r8X64_eq]

/-- The tensor bound of the literal description. -/
theorem e15xXWL_bnd : TBnd 64 (274877906944 * 15) e15xXWL := by
  rw [← e15xXW_eqL]
  exact e15xXW_bnd

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the source tensor. -/
theorem e15x_oddChkAh : OddDense.oddChk 64 (16777216 * 10496 / 2 ^ 16) true false e15xTW
    (TSplit.thi 64 16 e15XH) (4030464 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the source tensor. -/
theorem e15x_oddChkAl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e15xTW
    (TSplit.tlo 64 16 e15XH) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e15x_partA : oddWZ 64 true e15XH e15xVW = (264140488704 : ℤ) := by
  rw [TSplit.oddWZ_split 64 16 (by norm_num) true e15XH e15xVW,
    TSplit.oddWZ_of_chk2 true e15xVW e15xTW e15xVW_sh (TSplit.thi_bnd (by norm_num) e15XH_bnd) e15x_oddChkAh,
    TSplit.oddWZ_of_chk2 true e15xVW e15xTW e15xVW_sh (TSplit.tlo_bnd 64 16 (by norm_num) e15XH) e15x_oddChkAl]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e15x_oddChkBh : OddDense.oddChk 64 (274877906944 * 15 / 2 ^ 16) false true e15TH
    (TSplit.thi 64 16 e15xXWL) (256000 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e15x_oddChkBl : OddDense.oddChk 64 (2 ^ 16 - 1) false true e15TH
    (TSplit.tlo 64 16 e15xXWL) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e15x_partB : oddLZ 64 true e15xXW e15VH = (16777216000 : ℤ) := by
  rw [e15xXW_eqL, TSplit.oddLZ_split 64 16 (by norm_num) true e15xXWL e15VH,
    TSplit.oddLZ_of_chk2 true e15VH e15TH e15VH_sh (TSplit.thi_bnd (by norm_num) e15xXWL_bnd) e15x_oddChkBh,
    TSplit.oddLZ_of_chk2 true e15VH e15TH e15VH_sh (TSplit.tlo_bnd 64 16 (by norm_num) e15xXWL) e15x_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e15x_tchk : TSplit.tdotSplitChk 64 16 (4 * (16777216 * 10496)) (274877906944 * 15)
    (trialityTensorT 64 false e15XH) e15xXWL (35184372088832000 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e15x_partC : tdot 64 (trialityTensorT 64 false e15XH) e15xXW = (35184372088832000 : ℤ) := by
  rw [e15xXW_eqL, TSplit.tdot_of_splitChk (trialityTensorT_spec false e15XH_bnd (by norm_num)).1 e15xXWL_bnd e15x_tchk]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
