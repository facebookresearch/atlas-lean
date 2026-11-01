/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE13H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE13mW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Dense identification E13- (Seventh target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = false`) of `e13VH` (Eighth coset image) with `e13mVW` (Seventh image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e13m_EH : e13EH = 2097152 := by
  unfold e13EH
  rw [show tensorWordDenAll e13H = 256 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e13m_EW : e13mEW = 67108864 := by
  unfold e13mEW srcSeventhD0
  rw [show tensorWordDenAll e13mW = 8192 by decide, show tensorWordDenAll srcSeventhH = 4096 by decide]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the target against the triality image of the source tensor. -/
theorem e13m_oddChkA : OddDense.oddChk 64 (65536 * 10496) false true e13mTW e13XH (4294967296 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e13m_partA : oddWZ 64 false e13XH e13mVW = (4294967296 : ℤ) :=
  TSplit.oddWZ_of_chk2 false e13mVW e13mTW e13mVW_sh e13XH_bnd e13m_oddChkA

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e13m_oddChkBh : OddDense.oddChk 64 (274877906944 / 2 ^ 16) true false e13TH
    (TSplit.thi 64 16 e13mXW) (2015232 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e13m_oddChkBl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e13TH
    (TSplit.tlo 64 16 e13mXW) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e13m_partB : oddLZ 64 false e13mXW e13VH = (132070244352 : ℤ) := by
  rw [TSplit.oddLZ_split 64 16 (by norm_num) false e13mXW e13VH,
    TSplit.oddLZ_of_chk2 false e13VH e13TH e13VH_sh (TSplit.thi_bnd (by norm_num) e13mXW_tight) e13m_oddChkBh,
    TSplit.oddLZ_of_chk2 false e13VH e13TH e13VH_sh (TSplit.tlo_bnd 64 16 (by norm_num) e13mXW) e13m_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e13m_tchk : TSplit.tdotSplitChk 64 16 (4 * (65536 * 10496)) (274877906944)
    (trialityTensorT 64 true e13XH) e13mXW (16888498602639360 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e13m_partC : tdot 64 (trialityTensorT 64 true e13XH) e13mXW = (16888498602639360 : ℤ) := by
  rw [TSplit.tdot_of_splitChk (trialityTensorT_spec true e13XH_bnd (by norm_num)).1 e13mXW_tight e13m_tchk]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
