/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17mW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFamX64Root8
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification E17- (Root8 target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = false`) of `e17VH` (Eighth coset image) with `e17mVW` (Root8 image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e17m_EH : e17EH = 2097152 := by
  unfold e17EH
  rw [show tensorWordDenAll e17H = 256 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e17m_EW : e17mEW = 4194304 := by
  unfold e17mEW
  rw [show tensorWordDenAll e17mW = 131072 by decide]
  norm_num

/-- The packed tensor of the target image over the width-64 literal source tensor. -/
def e17mXWL : List SVec := tensorPlanS 64 e17mPlanW r8X64

/-- The two descriptions of the target tensor agree. -/
theorem e17mXW_eqL : e17mXW = e17mXWL := by
  unfold e17mXW e17mXWL
  rw [r8X64_eq]

/-- The tensor bound of the literal description. -/
theorem e17mXWL_bnd : TBnd 64 (34359738368 * 15) e17mXWL := by
  rw [← e17mXW_eqL]
  exact e17mXW_bnd

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the source tensor. -/
theorem e17m_oddChkAh : OddDense.oddChk 64 (65536 * 10496 / 2 ^ 16) false true e17mTW
    (TSplit.thi 64 16 e17XH) (253952 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the source tensor. -/
theorem e17m_oddChkAl : OddDense.oddChk 64 (2 ^ 16 - 1) false true e17mTW
    (TSplit.tlo 64 16 e17XH) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e17m_partA : oddWZ 64 false e17XH e17mVW = (16642998272 : ℤ) := by
  rw [TSplit.oddWZ_split 64 16 (by norm_num) false e17XH e17mVW,
    TSplit.oddWZ_of_chk2 false e17mVW e17mTW e17mVW_sh (TSplit.thi_bnd (by norm_num) e17XH_bnd) e17m_oddChkAh,
    TSplit.oddWZ_of_chk2 false e17mVW e17mTW e17mVW_sh (TSplit.tlo_bnd 64 16 (by norm_num) e17XH) e17m_oddChkAl]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e17m_oddChkBh : OddDense.oddChk 64 (34359738368 * 15 / 2 ^ 16) true false e17TH
    (TSplit.thi 64 16 e17mXWL) (129024 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e17m_oddChkBl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e17TH
    (TSplit.tlo 64 16 e17mXWL) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e17m_partB : oddLZ 64 false e17mXW e17VH = (8455716864 : ℤ) := by
  rw [e17mXW_eqL, TSplit.oddLZ_split 64 16 (by norm_num) false e17mXWL e17VH,
    TSplit.oddLZ_of_chk2 false e17VH e17TH e17VH_sh (TSplit.thi_bnd (by norm_num) e17mXWL_bnd) e17m_oddChkBh,
    TSplit.oddLZ_of_chk2 false e17VH e17TH e17VH_sh (TSplit.tlo_bnd 64 16 (by norm_num) e17mXWL) e17m_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e17m_tchk : TSplit.tdotSplitChk 64 16 (4 * (65536 * 10496)) (34359738368 * 15)
    (trialityTensorT 64 true e17XH) e17mXWL (1090715534753792 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e17m_partC : tdot 64 (trialityTensorT 64 true e17XH) e17mXW = (1090715534753792 : ℤ) := by
  rw [e17mXW_eqL, TSplit.tdot_of_splitChk (trialityTensorT_spec true e17XH_bnd (by norm_num)).1 e17mXWL_bnd e17m_tchk]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
