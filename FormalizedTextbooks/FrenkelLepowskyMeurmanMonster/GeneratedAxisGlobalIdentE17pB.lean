/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17pW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFamX64Twelfth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification E17+ (Twelfth target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = true`) of `e17VH` (Eighth coset image) with `e17pVW` (Twelfth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e17p_EH : e17EH = 2097152 := by
  unfold e17EH
  rw [show tensorWordDenAll e17H = 256 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e17p_EW : e17pEW = 16384 := by
  unfold e17pEW
  rw [show tensorWordDenAll e17pW = 512 by decide]
  norm_num

/-- The packed tensor of the target image over the width-64 literal source tensor. -/
def e17pXWL : List SVec := tensorPlanS 64 e17pPlanW twelfthX64

/-- The two descriptions of the target tensor agree. -/
theorem e17pXW_eqL : e17pXW = e17pXWL := by
  unfold e17pXW e17pXWL
  rw [twelfthX64_eq]

/-- The tensor bound of the literal description. -/
theorem e17pXWL_bnd : TBnd 64 (524288 * 15) e17pXWL := by
  rw [← e17pXW_eqL]
  exact e17pXW_bnd

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the source tensor. -/
theorem e17p_oddChkAh : OddDense.oddChk 64 (65536 * 10496 / 2 ^ 16) true false e17pTW
    (TSplit.thi 64 16 e17XH) (253952 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the source tensor. -/
theorem e17p_oddChkAl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e17pTW
    (TSplit.tlo 64 16 e17XH) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e17p_partA : oddWZ 64 true e17XH e17pVW = (16642998272 : ℤ) := by
  rw [TSplit.oddWZ_split 64 16 (by norm_num) true e17XH e17pVW,
    TSplit.oddWZ_of_chk2 true e17pVW e17pTW e17pVW_sh (TSplit.thi_bnd (by norm_num) e17XH_bnd) e17p_oddChkAh,
    TSplit.oddWZ_of_chk2 true e17pVW e17pTW e17pVW_sh (TSplit.tlo_bnd 64 16 (by norm_num) e17XH) e17p_oddChkAl]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the source against the tensor of the target. -/
theorem e17p_oddChkB : OddDense.oddChk 64 (524288 * 15) false true e17TH e17pXWL (33030144 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e17p_partB : oddLZ 64 true e17pXW e17VH = (33030144 : ℤ) := by
  rw [e17pXW_eqL, TSplit.oddLZ_of_chk2 true e17VH e17TH e17VH_sh e17pXWL_bnd e17p_oddChkB]

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e17p_tchk : TSplit.tdotSplitChk 64 16 (4 * (65536 * 10496)) (524288 * 15)
    (trialityTensorT 64 false e17XH) e17pXWL (4260607557632 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e17p_partC : tdot 64 (trialityTensorT 64 false e17XH) e17pXW = (4260607557632 : ℤ) := by
  rw [e17pXW_eqL, TSplit.tdot_of_splitChk (trialityTensorT_spec false e17XH_bnd (by norm_num)).1 e17pXWL_bnd e17p_tchk]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
