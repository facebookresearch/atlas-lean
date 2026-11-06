/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE15H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE15M
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast

/-! # Dense identification E15-: odd and tensor parts of the pairing

Pairing of the triality image (`fwd = false`) of `e15VH` with `e15VM` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e15m_EH : e15EH = 33554432 := by
  unfold e15EH
  rw [show tensorWordDenAll e15H = 4096 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e15m_EM : e15EM = 67108864 := by
  unfold e15EM
  rw [show tensorWordDenAll e15M = 8192 by decide, srcEighthH_den]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the source tensor. -/
theorem e15m_oddChkAh : OddDense.oddChk 64 (16777216 * 10496 / 2 ^ 16) false true e15TM
    (TSplit.thi 64 16 e15XH) (1024000 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the source tensor. -/
theorem e15m_oddChkAl : OddDense.oddChk 64 (2 ^ 16 - 1) false true e15TM
    (TSplit.tlo 64 16 e15XH) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e15m_partA : oddWZ 64 false e15XH e15VM = (67108864000 : ℤ) := by
  rw [TSplit.oddWZ_split 64 16 (by norm_num) false e15XH e15VM,
    TSplit.oddWZ_of_chk2 false e15VM e15TM e15VM_sh (TSplit.thi_bnd (by norm_num) e15XH_bnd)
      e15m_oddChkAh,
    TSplit.oddWZ_of_chk2 false e15VM e15TM e15VM_sh (TSplit.tlo_bnd 64 16 (by norm_num) e15XH)
      e15m_oddChkAl]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e15m_oddChkBh : OddDense.oddChk 64 (134217728 * 10496 / 2 ^ 16) true false e15TH
    (TSplit.thi 64 16 e15XM) (2048000 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e15m_oddChkBl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e15TH
    (TSplit.tlo 64 16 e15XM) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e15m_partB : oddLZ 64 false e15XM e15VH = (134217728000 : ℤ) := by
  rw [TSplit.oddLZ_split 64 16 (by norm_num) false e15XM e15VH,
    TSplit.oddLZ_of_chk2 false e15VH e15TH e15VH_sh (TSplit.thi_bnd (by norm_num) e15XM_bnd)
      e15m_oddChkBh,
    TSplit.oddLZ_of_chk2 false e15VH e15TH e15VH_sh (TSplit.tlo_bnd 64 16 (by norm_num) e15XM)
      e15m_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e15m_tchk : TSplit.tdotSplitChk 64 16 (4 * (16777216 * 10496)) (134217728 * 10496)
    (trialityTensorT 64 true e15XH) e15XM (276971377083285504 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e15m_partC : tdot 64 (trialityTensorT 64 true e15XH) e15XM = (276971377083285504 : ℤ) :=
  TSplit.tdot_of_splitChk (trialityTensorT_spec true e15XH_bnd (by norm_num)).1 e15XM_bnd e15m_tchk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
