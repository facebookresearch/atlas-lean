/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE3H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE3M
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast

/-! # Dense identification E3-: odd and tensor parts of the pairing

Pairing of the triality image (`fwd = false`) of `e3VH` with `e3VM` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e3m_EH : e3EH = 2097152 := by
  unfold e3EH
  rw [show tensorWordDenAll e3H = 256 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e3m_EM : e3EM = 4194304 := by
  unfold e3EM
  rw [show tensorWordDenAll e3M = 512 by decide, srcEighthH_den]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the target against the triality image of the source tensor. -/
theorem e3m_oddChkA : OddDense.oddChk 64 (65536 * 10496) false true e3TM e3XH (4076863488 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e3m_partA : oddWZ 64 false e3XH e3VM = (4076863488 : ℤ) :=
  TSplit.oddWZ_of_chk2 false e3VM e3TM e3VM_sh e3XH_bnd e3m_oddChkA

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e3m_oddChkBh : OddDense.oddChk 64 (524288 * 10496 / 2 ^ 16) true false e3TH
    (TSplit.thi 64 16 e3XM) (124416 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e3m_oddChkBl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e3TH
    (TSplit.tlo 64 16 e3XM) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e3m_partB : oddLZ 64 false e3XM e3VH = (8153726976 : ℤ) := by
  rw [TSplit.oddLZ_split 64 16 (by norm_num) false e3XM e3VH,
    TSplit.oddLZ_of_chk2 false e3VH e3TH e3VH_sh (TSplit.thi_bnd (by norm_num) e3XM_bnd)
      e3m_oddChkBh,
    TSplit.oddLZ_of_chk2 false e3VH e3TH e3VH_sh (TSplit.tlo_bnd 64 16 (by norm_num) e3XM)
      e3m_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e3m_tchk : TSplit.tdotSplitChk 64 16 (4 * (65536 * 10496)) (524288 * 10496)
    (trialityTensorT 64 true e3XH) e3XM (1112705767309312 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e3m_partC : tdot 64 (trialityTensorT 64 true e3XH) e3XM = (1112705767309312 : ℤ) :=
  TSplit.tdot_of_splitChk (trialityTensorT_spec true e3XH_bnd (by norm_num)).1 e3XM_bnd e3m_tchk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
