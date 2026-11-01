/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE24H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE24mW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Dense identification E24- (Seventh target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = false`) of `e24VH` (Eighth coset image) with `e24mVW` (Seventh image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e24m_EH : e24EH = 131072 := by
  unfold e24EH
  rw [show tensorWordDenAll e24H = 16 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e24m_EW : e24mEW = 4194304 := by
  unfold e24mEW srcSeventhD0
  rw [show tensorWordDenAll e24mW = 512 by decide, show tensorWordDenAll srcSeventhH = 4096 by decide]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the target against the triality image of the source tensor. -/
theorem e24m_oddChkA : OddDense.oddChk 64 (256 * 10496) false true e24mTW e24XH (260046848 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e24m_partA : oddWZ 64 false e24XH e24mVW = (260046848 : ℤ) :=
  TSplit.oddWZ_of_chk2 false e24mVW e24mTW e24mVW_sh e24XH_bnd e24m_oddChkA

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e24m_oddChkBh : OddDense.oddChk 64 (524288 * (4 * (16777216 * 8) + 276 * 6144) / 2 ^ 19) true false e24TH
    (TSplit.thi 64 19 e24mXW) (42520 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e24m_oddChkBl : OddDense.oddChk 64 (2 ^ 19 - 1) true false e24TH
    (TSplit.tlo 64 19 e24mXW) (-14306770944 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e24m_partB : oddLZ 64 false e24mXW e24VH = (7985954816 : ℤ) := by
  rw [TSplit.oddLZ_split 64 19 (by norm_num) false e24mXW e24VH,
    TSplit.oddLZ_of_chk2 false e24VH e24TH e24VH_sh (TSplit.thi_bnd (by norm_num) e24mXW_bnd) e24m_oddChkBh,
    TSplit.oddLZ_of_chk2 false e24VH e24TH e24VH_sh (TSplit.tlo_bnd 64 19 (by norm_num) e24mXW) e24m_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e24m_tchk : TSplit.tdotSplitChk 64 16 (4 * (256 * 10496)) (524288 * (4 * (16777216 * 8) + 276 * 6144))
    (trialityTensorT 64 true e24XH) e24mXW (68169720922112 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e24m_partC : tdot 64 (trialityTensorT 64 true e24XH) e24mXW = (68169720922112 : ℤ) := by
  rw [TSplit.tdot_of_splitChk (trialityTensorT_spec true e24XH_bnd (by norm_num)).1 e24mXW_bnd e24m_tchk]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
