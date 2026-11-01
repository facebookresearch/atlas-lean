/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE23H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE23mW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFamX64Root8
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification E23- (Root8 target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = false`) of `e23VH` (Eighth coset image) with `e23mVW` (Root8 image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e23m_EH : e23EH = 2097152 := by
  unfold e23EH
  rw [show tensorWordDenAll e23H = 256 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e23m_EW : e23mEW = 16384 := by
  unfold e23mEW
  rw [show tensorWordDenAll e23mW = 512 by decide]
  norm_num

/-- The packed tensor of the target image over the width-64 literal source tensor. -/
def e23mXWL : List SVec := tensorPlanS 64 e23mPlanW r8X64

/-- The two descriptions of the target tensor agree. -/
theorem e23mXW_eqL : e23mXW = e23mXWL := by
  unfold e23mXW e23mXWL
  rw [r8X64_eq]

/-- The tensor bound of the literal description. -/
theorem e23mXWL_bnd : TBnd 64 (524288 * 15) e23mXWL := by
  rw [← e23mXW_eqL]
  exact e23mXW_bnd

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the source tensor. -/
theorem e23m_oddChkAh : OddDense.oddChk 64 (65536 * 10496 / 2 ^ 16) false true e23mTW
    (TSplit.thi 64 16 e23XH) (254976 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the source tensor. -/
theorem e23m_oddChkAl : OddDense.oddChk 64 (2 ^ 16 - 1) false true e23mTW
    (TSplit.tlo 64 16 e23XH) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e23m_partA : oddWZ 64 false e23XH e23mVW = (16710107136 : ℤ) := by
  rw [TSplit.oddWZ_split 64 16 (by norm_num) false e23XH e23mVW,
    TSplit.oddWZ_of_chk2 false e23mVW e23mTW e23mVW_sh (TSplit.thi_bnd (by norm_num) e23XH_bnd) e23m_oddChkAh,
    TSplit.oddWZ_of_chk2 false e23mVW e23mTW e23mVW_sh (TSplit.tlo_bnd 64 16 (by norm_num) e23XH) e23m_oddChkAl]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the source against the tensor of the target. -/
theorem e23m_oddChkB : OddDense.oddChk 64 (524288 * 15) true false e23TH e23mXWL (33161216 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e23m_partB : oddLZ 64 false e23mXW e23VH = (33161216 : ℤ) := by
  rw [e23mXW_eqL, TSplit.oddLZ_of_chk2 false e23VH e23TH e23VH_sh e23mXWL_bnd e23m_oddChkB]

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e23m_tchk : TSplit.tdotSplitChk 64 16 (4 * (65536 * 10496)) (524288 * 15)
    (trialityTensorT 64 true e23XH) e23mXWL (4243427688448 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e23m_partC : tdot 64 (trialityTensorT 64 true e23XH) e23mXW = (4243427688448 : ℤ) := by
  rw [e23mXW_eqL, TSplit.tdot_of_splitChk (trialityTensorT_spec true e23XH_bnd (by norm_num)).1 e23mXWL_bnd e23m_tchk]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
