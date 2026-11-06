/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE21H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE21M
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast

/-! # Dense identification E21-: odd and tensor parts of the pairing

Pairing of the triality image (`fwd = false`) of `e21VH` with `e21VM` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e21m_EH : e21EH = 2097152 := by
  unfold e21EH
  rw [show tensorWordDenAll e21H = 256 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e21m_EM : e21EM = 4194304 := by
  unfold e21EM
  rw [show tensorWordDenAll e21M = 512 by decide, srcEighthH_den]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the target against the triality image of the source tensor. -/
theorem e21m_oddChkA : OddDense.oddChk 64 (65536 * 10496) false true e21TM e21XH (4076863488 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e21m_partA : oddWZ 64 false e21XH e21VM = (4076863488 : ℤ) :=
  TSplit.oddWZ_of_chk2 false e21VM e21TM e21VM_sh e21XH_bnd e21m_oddChkA

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e21m_oddChkBh : OddDense.oddChk 64 (524288 * 10496 / 2 ^ 16) true false e21TH
    (TSplit.thi 64 16 e21XM) (124416 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e21m_oddChkBl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e21TH
    (TSplit.tlo 64 16 e21XM) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e21m_partB : oddLZ 64 false e21XM e21VH = (8153726976 : ℤ) := by
  rw [TSplit.oddLZ_split 64 16 (by norm_num) false e21XM e21VH,
    TSplit.oddLZ_of_chk2 false e21VH e21TH e21VH_sh (TSplit.thi_bnd (by norm_num) e21XM_bnd)
      e21m_oddChkBh,
    TSplit.oddLZ_of_chk2 false e21VH e21TH e21VH_sh (TSplit.tlo_bnd 64 16 (by norm_num) e21XM)
      e21m_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e21m_tchk : TSplit.tdotSplitChk 64 16 (4 * (65536 * 10496)) (524288 * 10496)
    (trialityTensorT 64 true e21XH) e21XM (1112705767309312 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e21m_partC : tdot 64 (trialityTensorT 64 true e21XH) e21XM = (1112705767309312 : ℤ) :=
  TSplit.tdot_of_splitChk (trialityTensorT_spec true e21XH_bnd (by norm_num)).1 e21XM_bnd e21m_tchk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
