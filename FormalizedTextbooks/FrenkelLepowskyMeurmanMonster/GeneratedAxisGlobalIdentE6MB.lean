/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE6H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE6M
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ

/-! # Dense identification E6-: odd and tensor parts of the pairing

Pairing of the triality image (`fwd = false`) of `e6VH` with `e6VM` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e6m_EH : e6EH = 2097152 := by
  unfold e6EH
  rw [show tensorWordDenAll e6H = 256 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e6m_EM : e6EM = 4194304 := by
  unfold e6EM
  rw [show tensorWordDenAll e6M = 512 by decide, srcEighthH_den]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the target against the triality image of the source tensor. -/
theorem e6m_oddChkA : OddDense.oddChk 64 (65536 * 10496) false true e6TM e6XH (4160749568 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e6m_partA : oddWZ 64 false e6XH e6VM = (4160749568 : ℤ) :=
  TSplit.oddWZ_of_chk2 false e6VM e6TM e6VM_sh e6XH_bnd e6m_oddChkA

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e6m_oddChkBh : OddDense.oddChk 64 (524288 * 10496 / 2 ^ 16) true false e6TH
    (TSplit.thi 64 16 e6XM) (126976 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e6m_oddChkBl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e6TH
    (TSplit.tlo 64 16 e6XM) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e6m_partB : oddLZ 64 false e6XM e6VH = (8321499136 : ℤ) := by
  rw [TSplit.oddLZ_split 64 16 (by norm_num) false e6XM e6VH,
    TSplit.oddLZ_of_chk2 false e6VH e6TH e6VH_sh (TSplit.thi_bnd (by norm_num) e6XM_bnd)
      e6m_oddChkBh,
    TSplit.oddLZ_of_chk2 false e6VH e6TH e6VH_sh (TSplit.tlo_bnd 64 16 (by norm_num) e6XM)
      e6m_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e6m_tchk : TSplit.tdotSplitChk 64 16 (4 * (65536 * 10496)) (524288 * 10496)
    (trialityTensorT 64 true e6XH) e6XM (1090715534753792 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e6m_partC : tdot 64 (trialityTensorT 64 true e6XH) e6XM = (1090715534753792 : ℤ) :=
  TSplit.tdot_of_splitChk (trialityTensorT_spec true e6XH_bnd (by norm_num)).1 e6XM_bnd e6m_tchk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
