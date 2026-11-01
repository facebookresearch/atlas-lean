/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE35H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE35P
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast

/-! # Dense identification E35+: odd and tensor parts of the pairing

Pairing of the triality image (`fwd = true`) of `e35VH` with `e35VP` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e35p_EH : e35EH = 33554432 := by
  unfold e35EH
  rw [show tensorWordDenAll e35H = 4096 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e35p_EP : e35EP = 67108864 := by
  unfold e35EP
  rw [show tensorWordDenAll e35P = 8192 by decide, srcEighthH_den]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the source tensor. -/
theorem e35p_oddChkAh : OddDense.oddChk 64 (16777216 * 10496 / 2 ^ 16) true false e35TP
    (TSplit.thi 64 16 e35XH) (1024000 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the source tensor. -/
theorem e35p_oddChkAl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e35TP
    (TSplit.tlo 64 16 e35XH) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e35p_partA : oddWZ 64 true e35XH e35VP = (67108864000 : ℤ) := by
  rw [TSplit.oddWZ_split 64 16 (by norm_num) true e35XH e35VP,
    TSplit.oddWZ_of_chk2 true e35VP e35TP e35VP_sh (TSplit.thi_bnd (by norm_num) e35XH_bnd)
      e35p_oddChkAh,
    TSplit.oddWZ_of_chk2 true e35VP e35TP e35VP_sh (TSplit.tlo_bnd 64 16 (by norm_num) e35XH)
      e35p_oddChkAl]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e35p_oddChkBh : OddDense.oddChk 64 (134217728 * 10496 / 2 ^ 16) false true e35TH
    (TSplit.thi 64 16 e35XP) (2048000 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e35p_oddChkBl : OddDense.oddChk 64 (2 ^ 16 - 1) false true e35TH
    (TSplit.tlo 64 16 e35XP) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e35p_partB : oddLZ 64 true e35XP e35VH = (134217728000 : ℤ) := by
  rw [TSplit.oddLZ_split 64 16 (by norm_num) true e35XP e35VH,
    TSplit.oddLZ_of_chk2 true e35VH e35TH e35VH_sh (TSplit.thi_bnd (by norm_num) e35XP_bnd)
      e35p_oddChkBh,
    TSplit.oddLZ_of_chk2 true e35VH e35TH e35VH_sh (TSplit.tlo_bnd 64 16 (by norm_num) e35XP)
      e35p_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e35p_tchk : TSplit.tdotSplitChk 64 16 (4 * (16777216 * 10496)) (134217728 * 10496)
    (trialityTensorT 64 false e35XH) e35XP (276971377083285504 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e35p_partC : tdot 64 (trialityTensorT 64 false e35XH) e35XP = (276971377083285504 : ℤ) :=
  TSplit.tdot_of_splitChk (trialityTensorT_spec false e35XH_bnd (by norm_num)).1 e35XP_bnd e35p_tchk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
