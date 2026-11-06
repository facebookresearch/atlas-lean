/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE23H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE23pW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFamX64Tenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Dense identification E23+ (Tenth target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = true`) of `e23VH` (Eighth coset image) with `e23pVW` (Tenth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e23p_EH : e23EH = 2097152 := by
  unfold e23EH
  rw [show tensorWordDenAll e23H = 256 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e23p_EW : e23pEW = 134217728 := by
  unfold e23pEW
  rw [show tensorWordDenAll e23pW = 4194304 by decide]
  norm_num

/-- The packed tensor of the target image over the width-64 literal source tensor. -/
def e23pXWL : List SVec := tensorPlanS 64 e23pPlanW tenthX64

/-- The two descriptions of the target tensor agree. -/
theorem e23pXW_eqL : e23pXW = e23pXWL := by
  unfold e23pXW e23pXWL
  rw [tenthX64_eq]

/-- The tensor bound of the literal description. -/
theorem e23pXWL_bnd : TBnd 64 (70368744177664 * 15) e23pXWL := by
  rw [← e23pXW_eqL]
  exact e23pXW_bnd

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the source tensor. -/
theorem e23p_oddChkAh : OddDense.oddChk 64 (65536 * 10496 / 2 ^ 16) true false e23pTW
    (TSplit.thi 64 16 e23XH) (252928 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the source tensor. -/
theorem e23p_oddChkAl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e23pTW
    (TSplit.tlo 64 16 e23XH) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e23p_partA : oddWZ 64 true e23XH e23pVW = (16575889408 : ℤ) := by
  rw [TSplit.oddWZ_split 64 16 (by norm_num) true e23XH e23pVW,
    TSplit.oddWZ_of_chk2 true e23pVW e23pTW e23pVW_sh (TSplit.thi_bnd (by norm_num) e23XH_bnd) e23p_oddChkAh,
    TSplit.oddWZ_of_chk2 true e23pVW e23pTW e23pVW_sh (TSplit.tlo_bnd 64 16 (by norm_num) e23XH) e23p_oddChkAl]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e23p_oddChkBh : OddDense.oddChk 64 (70368744177664 * 15 / 2 ^ 21) false true e23TH
    (TSplit.thi 64 21 e23pXWL) (129536 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e23p_oddChkBl : OddDense.oddChk 64 (2 ^ 21 - 1) false true e23TH
    (TSplit.tlo 64 21 e23pXWL) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e23p_partB : oddLZ 64 true e23pXW e23VH = (271656681472 : ℤ) := by
  rw [e23pXW_eqL, TSplit.oddLZ_split 64 21 (by norm_num) true e23pXWL e23VH,
    TSplit.oddLZ_of_chk2 true e23VH e23TH e23VH_sh (TSplit.thi_bnd (by norm_num) e23pXWL_bnd) e23p_oddChkBh,
    TSplit.oddLZ_of_chk2 true e23VH e23TH e23VH_sh (TSplit.tlo_bnd 64 21 (by norm_num) e23pXWL) e23p_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e23p_tchk : TSplit.tdotSplitChk 64 16 (4 * (65536 * 10496)) (70368744177664 * 15)
    (trialityTensorT 64 false e23XH) e23pXWL (35043634600476672 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e23p_partC : tdot 64 (trialityTensorT 64 false e23XH) e23pXW = (35043634600476672 : ℤ) := by
  rw [e23pXW_eqL, TSplit.tdot_of_splitChk (trialityTensorT_spec false e23XH_bnd (by norm_num)).1 e23pXWL_bnd e23p_tchk]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
