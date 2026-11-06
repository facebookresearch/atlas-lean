/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE12H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE12P
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast

/-! # Dense identification E12+: odd and tensor parts of the pairing

Pairing of the triality image (`fwd = true`) of `e12VH` with `e12VP` (`pairTriGZT`), each part one
kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e12p_EH : e12EH = 2097152 := by
  unfold e12EH
  rw [show tensorWordDenAll e12H = 256 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e12p_EP : e12EP = 4194304 := by
  unfold e12EP
  rw [show tensorWordDenAll e12P = 512 by decide, srcEighthH_den]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the target against the triality image of the source tensor. -/
theorem e12p_oddChkA : OddDense.oddChk 64 (65536 * 10496) true false e12TP e12XH (4211081216 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e12p_partA : oddWZ 64 true e12XH e12VP = (4211081216 : ℤ) :=
  TSplit.oddWZ_of_chk2 true e12VP e12TP e12VP_sh e12XH_bnd e12p_oddChkA

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e12p_oddChkBh : OddDense.oddChk 64 (524288 * 10496 / 2 ^ 16) false true e12TH
    (TSplit.thi 64 16 e12XP) (128512 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e12p_oddChkBl : OddDense.oddChk 64 (2 ^ 16 - 1) false true e12TH
    (TSplit.tlo 64 16 e12XP) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e12p_partB : oddLZ 64 true e12XP e12VH = (8422162432 : ℤ) := by
  rw [TSplit.oddLZ_split 64 16 (by norm_num) true e12XP e12VH,
    TSplit.oddLZ_of_chk2 true e12VH e12TH e12VH_sh (TSplit.thi_bnd (by norm_num) e12XP_bnd)
      e12p_oddChkBh,
    TSplit.oddLZ_of_chk2 true e12VH e12TH e12VH_sh (TSplit.tlo_bnd 64 16 (by norm_num) e12XP)
      e12p_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e12p_tchk : TSplit.tdotSplitChk 64 16 (4 * (65536 * 10496)) (524288 * 10496)
    (trialityTensorT 64 false e12XH) e12XP (1077521395220480 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e12p_partC : tdot 64 (trialityTensorT 64 false e12XH) e12XP = (1077521395220480 : ℤ) :=
  TSplit.tdot_of_splitChk (trialityTensorT_spec false e12XH_bnd (by norm_num)).1 e12XP_bnd e12p_tchk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
