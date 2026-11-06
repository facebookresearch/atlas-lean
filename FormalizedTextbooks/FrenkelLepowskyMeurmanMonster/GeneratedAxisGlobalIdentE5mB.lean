/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE5H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE5mW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFamX64Twelfth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification E5- (Twelfth target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = false`) of `e5VH` (Eighth coset image) with `e5mVW` (Twelfth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e5m_EH : e5EH = 2097152 := by
  unfold e5EH
  rw [show tensorWordDenAll e5H = 256 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e5m_EW : e5mEW = 16384 := by
  unfold e5mEW
  rw [show tensorWordDenAll e5mW = 512 by decide]
  norm_num

/-- The packed tensor of the target image over the width-64 literal source tensor. -/
def e5mXWL : List SVec := tensorPlanS 64 e5mPlanW twelfthX64

/-- The two descriptions of the target tensor agree. -/
theorem e5mXW_eqL : e5mXW = e5mXWL := by
  unfold e5mXW e5mXWL
  rw [twelfthX64_eq]

/-- The tensor bound of the literal description. -/
theorem e5mXWL_bnd : TBnd 64 (524288 * 15) e5mXWL := by
  rw [← e5mXW_eqL]
  exact e5mXW_bnd

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the source tensor. -/
theorem e5m_oddChkAh : OddDense.oddChk 64 (65536 * 10496 / 2 ^ 16) false true e5mTW
    (TSplit.thi 64 16 e5XH) (253952 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the source tensor. -/
theorem e5m_oddChkAl : OddDense.oddChk 64 (2 ^ 16 - 1) false true e5mTW
    (TSplit.tlo 64 16 e5XH) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e5m_partA : oddWZ 64 false e5XH e5mVW = (16642998272 : ℤ) := by
  rw [TSplit.oddWZ_split 64 16 (by norm_num) false e5XH e5mVW,
    TSplit.oddWZ_of_chk2 false e5mVW e5mTW e5mVW_sh (TSplit.thi_bnd (by norm_num) e5XH_bnd) e5m_oddChkAh,
    TSplit.oddWZ_of_chk2 false e5mVW e5mTW e5mVW_sh (TSplit.tlo_bnd 64 16 (by norm_num) e5XH) e5m_oddChkAl]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the source against the tensor of the target. -/
theorem e5m_oddChkB : OddDense.oddChk 64 (524288 * 15) true false e5TH e5mXWL (33030144 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e5m_partB : oddLZ 64 false e5mXW e5VH = (33030144 : ℤ) := by
  rw [e5mXW_eqL, TSplit.oddLZ_of_chk2 false e5VH e5TH e5VH_sh e5mXWL_bnd e5m_oddChkB]

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e5m_tchk : TSplit.tdotSplitChk 64 16 (4 * (65536 * 10496)) (524288 * 15)
    (trialityTensorT 64 true e5XH) e5mXWL (4260607557632 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e5m_partC : tdot 64 (trialityTensorT 64 true e5XH) e5mXW = (4260607557632 : ℤ) := by
  rw [e5mXW_eqL, TSplit.tdot_of_splitChk (trialityTensorT_spec true e5XH_bnd (by norm_num)).1 e5mXWL_bnd e5m_tchk]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
