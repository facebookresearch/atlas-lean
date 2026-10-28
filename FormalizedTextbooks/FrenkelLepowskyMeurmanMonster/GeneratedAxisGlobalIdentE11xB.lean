/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11xW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFamX64Twelfth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification E11- (Twelfth target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = false`) of `e11VH` (Eighth coset image) with `e11xVW` (Twelfth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e11x_EH : e11EH = 33554432 := by
  unfold e11EH
  rw [show tensorWordDenAll e11H = 4096 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e11x_EW : e11xEW = 16384 := by
  unfold e11xEW
  rw [show tensorWordDenAll e11xW = 512 by decide]
  norm_num

/-- The packed tensor of the target image over the width-64 literal source tensor. -/
def e11xXWL : List SVec := tensorPlanS 64 e11xPlanW twelfthX64

/-- The two descriptions of the target tensor agree. -/
theorem e11xXW_eqL : e11xXW = e11xXWL := by
  unfold e11xXW e11xXWL
  rw [twelfthX64_eq]

/-- The tensor bound of the literal description. -/
theorem e11xXWL_bnd : TBnd 64 (524288 * 15) e11xXWL := by
  rw [← e11xXW_eqL]
  exact e11xXW_bnd

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the source tensor. -/
theorem e11x_oddChkAh : OddDense.oddChk 64 (16777216 * 10496 / 2 ^ 16) false true e11xTW
    (TSplit.thi 64 16 e11XH) (4030464 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the source tensor. -/
theorem e11x_oddChkAl : OddDense.oddChk 64 (2 ^ 16 - 1) false true e11xTW
    (TSplit.tlo 64 16 e11XH) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e11x_partA : oddWZ 64 false e11XH e11xVW = (264140488704 : ℤ) := by
  rw [TSplit.oddWZ_split 64 16 (by norm_num) false e11XH e11xVW,
    TSplit.oddWZ_of_chk2 false e11xVW e11xTW e11xVW_sh (TSplit.thi_bnd (by norm_num) e11XH_bnd) e11x_oddChkAh,
    TSplit.oddWZ_of_chk2 false e11xVW e11xTW e11xVW_sh (TSplit.tlo_bnd 64 16 (by norm_num) e11XH) e11x_oddChkAl]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the source against the tensor of the target. -/
theorem e11x_oddChkB : OddDense.oddChk 64 (524288 * 15) true false e11TH e11xXWL (32768000 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e11x_partB : oddLZ 64 false e11xXW e11VH = (32768000 : ℤ) := by
  rw [e11xXW_eqL, TSplit.oddLZ_of_chk2 false e11VH e11TH e11VH_sh e11xXWL_bnd e11x_oddChkB]

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e11x_tchk : TSplit.tdotSplitChk 64 16 (4 * (16777216 * 10496)) (524288 * 15)
    (trialityTensorT 64 true e11XH) e11xXWL (68719476736000 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e11x_partC : tdot 64 (trialityTensorT 64 true e11XH) e11xXW = (68719476736000 : ℤ) := by
  rw [e11xXW_eqL, TSplit.tdot_of_splitChk (trialityTensorT_spec true e11XH_bnd (by norm_num)).1 e11xXWL_bnd e11x_tchk]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
