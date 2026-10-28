/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE16H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE16mW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFamX64Root8
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification E16- (Root8 target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = false`) of `e16VH` (Eighth coset image) with `e16mVW` (Root8 image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e16m_EH : e16EH = 2097152 := by
  unfold e16EH
  rw [show tensorWordDenAll e16H = 256 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e16m_EW : e16mEW = 524288 := by
  unfold e16mEW
  rw [show tensorWordDenAll e16mW = 16384 by decide]
  norm_num

/-- The packed tensor of the target image over the width-64 literal source tensor. -/
def e16mXWL : List SVec := tensorPlanS 64 e16mPlanW r8X64

/-- The two descriptions of the target tensor agree. -/
theorem e16mXW_eqL : e16mXW = e16mXWL := by
  unfold e16mXW e16mXWL
  rw [r8X64_eq]

/-- The tensor bound of the literal description. -/
theorem e16mXWL_bnd : TBnd 64 (1073741824 * 15) e16mXWL := by
  rw [← e16mXW_eqL]
  exact e16mXW_bnd

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the source tensor. -/
theorem e16m_oddChkAh : OddDense.oddChk 64 (65536 * 10496 / 2 ^ 16) false true e16mTW
    (TSplit.thi 64 16 e16XH) (253952 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the source tensor. -/
theorem e16m_oddChkAl : OddDense.oddChk 64 (2 ^ 16 - 1) false true e16mTW
    (TSplit.tlo 64 16 e16XH) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e16m_partA : oddWZ 64 false e16XH e16mVW = (16642998272 : ℤ) := by
  rw [TSplit.oddWZ_split 64 16 (by norm_num) false e16XH e16mVW,
    TSplit.oddWZ_of_chk2 false e16mVW e16mTW e16mVW_sh (TSplit.thi_bnd (by norm_num) e16XH_bnd) e16m_oddChkAh,
    TSplit.oddWZ_of_chk2 false e16mVW e16mTW e16mVW_sh (TSplit.tlo_bnd 64 16 (by norm_num) e16XH) e16m_oddChkAl]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e16m_oddChkBh : OddDense.oddChk 64 (1073741824 * 15 / 2 ^ 16) true false e16TH
    (TSplit.thi 64 16 e16mXWL) (40160 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e16m_oddChkBl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e16TH
    (TSplit.tlo 64 16 e16mXWL) (-1574961152 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e16m_partB : oddLZ 64 false e16mXW e16VH = (1056964608 : ℤ) := by
  rw [e16mXW_eqL, TSplit.oddLZ_split 64 16 (by norm_num) false e16mXWL e16VH,
    TSplit.oddLZ_of_chk2 false e16VH e16TH e16VH_sh (TSplit.thi_bnd (by norm_num) e16mXWL_bnd) e16m_oddChkBh,
    TSplit.oddLZ_of_chk2 false e16VH e16TH e16VH_sh (TSplit.tlo_bnd 64 16 (by norm_num) e16mXWL) e16m_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e16m_tchk : TSplit.tdotSplitChk 64 16 (4 * (65536 * 10496)) (1073741824 * 15)
    (trialityTensorT 64 true e16XH) e16mXWL (136339441844224 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e16m_partC : tdot 64 (trialityTensorT 64 true e16XH) e16mXW = (136339441844224 : ℤ) := by
  rw [e16mXW_eqL, TSplit.tdot_of_splitChk (trialityTensorT_spec true e16XH_bnd (by norm_num)).1 e16mXWL_bnd e16m_tchk]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
