/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE13H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE13pW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFamX64Tenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Dense identification E13+ (Tenth target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = true`) of `e13VH` (Eighth coset image) with `e13pVW` (Tenth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e13p_EH : e13EH = 2097152 := by
  unfold e13EH
  rw [show tensorWordDenAll e13H = 256 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e13p_EW : e13pEW = 16384 := by
  unfold e13pEW
  rw [show tensorWordDenAll e13pW = 512 by decide]
  norm_num

/-- The packed tensor of the target image over the width-64 literal source tensor. -/
def e13pXWL : List SVec := tensorPlanS 64 e13pPlanW tenthX64

/-- The two descriptions of the target tensor agree. -/
theorem e13pXW_eqL : e13pXW = e13pXWL := by
  unfold e13pXW e13pXWL
  rw [tenthX64_eq]

/-- The tensor bound of the literal description. -/
theorem e13pXWL_bnd : TBnd 64 (524288 * 15) e13pXWL := by
  rw [← e13pXW_eqL]
  exact e13pXW_bnd

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the source tensor. -/
theorem e13p_oddChkAh : OddDense.oddChk 64 (65536 * 10496 / 2 ^ 16) true false e13pTW
    (TSplit.thi 64 16 e13XH) (245760 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the source tensor. -/
theorem e13p_oddChkAl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e13pTW
    (TSplit.tlo 64 16 e13XH) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e13p_partA : oddWZ 64 true e13XH e13pVW = (16106127360 : ℤ) := by
  rw [TSplit.oddWZ_split 64 16 (by norm_num) true e13XH e13pVW,
    TSplit.oddWZ_of_chk2 true e13pVW e13pTW e13pVW_sh (TSplit.thi_bnd (by norm_num) e13XH_bnd) e13p_oddChkAh,
    TSplit.oddWZ_of_chk2 true e13pVW e13pTW e13pVW_sh (TSplit.tlo_bnd 64 16 (by norm_num) e13XH) e13p_oddChkAl]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the source against the tensor of the target. -/
theorem e13p_oddChkB : OddDense.oddChk 64 (524288 * 15) false true e13TH e13pXWL (32243712 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e13p_partB : oddLZ 64 true e13pXW e13VH = (32243712 : ℤ) := by
  rw [e13pXW_eqL, TSplit.oddLZ_of_chk2 true e13VH e13TH e13VH_sh e13pXWL_bnd e13p_oddChkB]

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e13p_tchk : TSplit.tdotSplitChk 64 16 (4 * (65536 * 10496)) (524288 * 15)
    (trialityTensorT 64 false e13XH) e13pXWL (4398046511104 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e13p_partC : tdot 64 (trialityTensorT 64 false e13XH) e13pXW = (4398046511104 : ℤ) := by
  rw [e13pXW_eqL, TSplit.tdot_of_splitChk (trialityTensorT_spec false e13XH_bnd (by norm_num)).1 e13pXWL_bnd e13p_tchk]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
