/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE29H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE29pW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFamX64Twelfth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification E29+ (Twelfth target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = true`) of `e29VH` (Eighth coset image) with `e29pVW` (Twelfth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e29p_EH : e29EH = 33554432 := by
  unfold e29EH
  rw [show tensorWordDenAll e29H = 4096 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e29p_EW : e29pEW = 262144 := by
  unfold e29pEW
  rw [show tensorWordDenAll e29pW = 8192 by decide]
  norm_num

/-- The packed tensor of the target image over the width-64 literal source tensor. -/
def e29pXWL : List SVec := tensorPlanS 64 e29pPlanW twelfthX64

/-- The two descriptions of the target tensor agree. -/
theorem e29pXW_eqL : e29pXW = e29pXWL := by
  unfold e29pXW e29pXWL
  rw [twelfthX64_eq]

/-- The tensor bound of the literal description. -/
theorem e29pXWL_bnd : TBnd 64 (134217728 * 15) e29pXWL := by
  rw [← e29pXW_eqL]
  exact e29pXW_bnd

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the source tensor. -/
theorem e29p_oddChkAh : OddDense.oddChk 64 (16777216 * 10496 / 2 ^ 16) true false e29pTW
    (TSplit.thi 64 16 e29XH) (4063232 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the source tensor. -/
theorem e29p_oddChkAl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e29pTW
    (TSplit.tlo 64 16 e29XH) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e29p_partA : oddWZ 64 true e29XH e29pVW = (266287972352 : ℤ) := by
  rw [TSplit.oddWZ_split 64 16 (by norm_num) true e29XH e29pVW,
    TSplit.oddWZ_of_chk2 true e29pVW e29pTW e29pVW_sh (TSplit.thi_bnd (by norm_num) e29XH_bnd) e29p_oddChkAh,
    TSplit.oddWZ_of_chk2 true e29pVW e29pTW e29pVW_sh (TSplit.tlo_bnd 64 16 (by norm_num) e29XH) e29p_oddChkAl]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e29p_oddChkBh : OddDense.oddChk 64 (134217728 * 15 / 2 ^ 16) false true e29TH
    (TSplit.thi 64 16 e29pXWL) (2112 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e29p_oddChkBl : OddDense.oddChk 64 (2 ^ 16 - 1) false true e29TH
    (TSplit.tlo 64 16 e29pXWL) (390070272 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e29p_partB : oddLZ 64 true e29pXW e29VH = (528482304 : ℤ) := by
  rw [e29pXW_eqL, TSplit.oddLZ_split 64 16 (by norm_num) true e29pXWL e29VH,
    TSplit.oddLZ_of_chk2 true e29VH e29TH e29VH_sh (TSplit.thi_bnd (by norm_num) e29pXWL_bnd) e29p_oddChkBh,
    TSplit.oddLZ_of_chk2 true e29VH e29TH e29VH_sh (TSplit.tlo_bnd 64 16 (by norm_num) e29pXWL) e29p_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e29p_tchk : TSplit.tdotSplitChk 64 16 (4 * (16777216 * 10496)) (134217728 * 15)
    (trialityTensorT 64 false e29XH) e29pXWL (1090715534753792 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e29p_partC : tdot 64 (trialityTensorT 64 false e29XH) e29pXW = (1090715534753792 : ℤ) := by
  rw [e29pXW_eqL, TSplit.tdot_of_splitChk (trialityTensorT_spec false e29XH_bnd (by norm_num)).1 e29pXWL_bnd e29p_tchk]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
