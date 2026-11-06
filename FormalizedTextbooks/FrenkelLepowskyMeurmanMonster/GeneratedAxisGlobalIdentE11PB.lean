/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11P
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast

/-! # Dense identification E11+: odd and tensor parts of the pairing

Pairing of the triality image (`fwd = true`) of `e11VH` with `e11VP` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e11p_EH : e11EH = 33554432 := by
  unfold e11EH
  rw [show tensorWordDenAll e11H = 4096 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e11p_EP : e11EP = 67108864 := by
  unfold e11EP
  rw [show tensorWordDenAll e11P = 8192 by decide, srcEighthH_den]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the source tensor. -/
theorem e11p_oddChkAh : OddDense.oddChk 64 (16777216 * 10496 / 2 ^ 16) true false e11TP
    (TSplit.thi 64 16 e11XH) (1024000 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the source tensor. -/
theorem e11p_oddChkAl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e11TP
    (TSplit.tlo 64 16 e11XH) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e11p_partA : oddWZ 64 true e11XH e11VP = (67108864000 : ℤ) := by
  rw [TSplit.oddWZ_split 64 16 (by norm_num) true e11XH e11VP,
    TSplit.oddWZ_of_chk2 true e11VP e11TP e11VP_sh (TSplit.thi_bnd (by norm_num) e11XH_bnd)
      e11p_oddChkAh,
    TSplit.oddWZ_of_chk2 true e11VP e11TP e11VP_sh (TSplit.tlo_bnd 64 16 (by norm_num) e11XH)
      e11p_oddChkAl]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e11p_oddChkBh : OddDense.oddChk 64 (134217728 * 10496 / 2 ^ 16) false true e11TH
    (TSplit.thi 64 16 e11XP) (2048000 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e11p_oddChkBl : OddDense.oddChk 64 (2 ^ 16 - 1) false true e11TH
    (TSplit.tlo 64 16 e11XP) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e11p_partB : oddLZ 64 true e11XP e11VH = (134217728000 : ℤ) := by
  rw [TSplit.oddLZ_split 64 16 (by norm_num) true e11XP e11VH,
    TSplit.oddLZ_of_chk2 true e11VH e11TH e11VH_sh (TSplit.thi_bnd (by norm_num) e11XP_bnd)
      e11p_oddChkBh,
    TSplit.oddLZ_of_chk2 true e11VH e11TH e11VH_sh (TSplit.tlo_bnd 64 16 (by norm_num) e11XP)
      e11p_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e11p_tchk : TSplit.tdotSplitChk 64 16 (4 * (16777216 * 10496)) (134217728 * 10496)
    (trialityTensorT 64 false e11XH) e11XP (276971377083285504 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e11p_partC : tdot 64 (trialityTensorT 64 false e11XH) e11XP = (276971377083285504 : ℤ) :=
  TSplit.tdot_of_splitChk (trialityTensorT_spec false e11XH_bnd (by norm_num)).1 e11XP_bnd e11p_tchk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
