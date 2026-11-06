/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE16H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE16pW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFamX64Root8
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification E16+ (Root8 target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = true`) of `e16VH` (Eighth coset image) with `e16pVW` (Root8 image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e16p_EH : e16EH = 2097152 := by
  unfold e16EH
  rw [show tensorWordDenAll e16H = 256 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e16p_EW : e16pEW = 524288 := by
  unfold e16pEW
  rw [show tensorWordDenAll e16pW = 16384 by decide]
  norm_num

/-- The packed tensor of the target image over the width-64 literal source tensor. -/
def e16pXWL : List SVec := tensorPlanS 64 e16pPlanW r8X64

/-- The two descriptions of the target tensor agree. -/
theorem e16pXW_eqL : e16pXW = e16pXWL := by
  unfold e16pXW e16pXWL
  rw [r8X64_eq]

/-- The tensor bound of the literal description. -/
theorem e16pXWL_bnd : TBnd 64 (1073741824 * 15) e16pXWL := by
  rw [← e16pXW_eqL]
  exact e16pXW_bnd

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the source tensor. -/
theorem e16p_oddChkAh : OddDense.oddChk 64 (65536 * 10496 / 2 ^ 16) true false e16pTW
    (TSplit.thi 64 16 e16XH) (253952 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the source tensor. -/
theorem e16p_oddChkAl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e16pTW
    (TSplit.tlo 64 16 e16XH) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e16p_partA : oddWZ 64 true e16XH e16pVW = (16642998272 : ℤ) := by
  rw [TSplit.oddWZ_split 64 16 (by norm_num) true e16XH e16pVW,
    TSplit.oddWZ_of_chk2 true e16pVW e16pTW e16pVW_sh (TSplit.thi_bnd (by norm_num) e16XH_bnd) e16p_oddChkAh,
    TSplit.oddWZ_of_chk2 true e16pVW e16pTW e16pVW_sh (TSplit.tlo_bnd 64 16 (by norm_num) e16XH) e16p_oddChkAl]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e16p_oddChkBh : OddDense.oddChk 64 (1073741824 * 15 / 2 ^ 16) false true e16TH
    (TSplit.thi 64 16 e16pXWL) (40520 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e16p_oddChkBl : OddDense.oddChk 64 (2 ^ 16 - 1) false true e16TH
    (TSplit.tlo 64 16 e16pXWL) (-1598554112 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e16p_partB : oddLZ 64 true e16pXW e16VH = (1056964608 : ℤ) := by
  rw [e16pXW_eqL, TSplit.oddLZ_split 64 16 (by norm_num) true e16pXWL e16VH,
    TSplit.oddLZ_of_chk2 true e16VH e16TH e16VH_sh (TSplit.thi_bnd (by norm_num) e16pXWL_bnd) e16p_oddChkBh,
    TSplit.oddLZ_of_chk2 true e16VH e16TH e16VH_sh (TSplit.tlo_bnd 64 16 (by norm_num) e16pXWL) e16p_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e16p_tchk : TSplit.tdotSplitChk 64 16 (4 * (65536 * 10496)) (1073741824 * 15)
    (trialityTensorT 64 false e16XH) e16pXWL (136339441844224 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e16p_partC : tdot 64 (trialityTensorT 64 false e16XH) e16pXW = (136339441844224 : ℤ) := by
  rw [e16pXW_eqL, TSplit.tdot_of_splitChk (trialityTensorT_spec false e16XH_bnd (by norm_num)).1 e16pXWL_bnd e16p_tchk]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
