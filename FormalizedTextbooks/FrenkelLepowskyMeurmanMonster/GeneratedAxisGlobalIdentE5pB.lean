/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE5H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE5pW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFamX64Twelfth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification E5+ (Twelfth target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = true`) of `e5VH` (Eighth coset image) with `e5pVW` (Twelfth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e5p_EH : e5EH = 2097152 := by
  unfold e5EH
  rw [show tensorWordDenAll e5H = 256 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e5p_EW : e5pEW = 16384 := by
  unfold e5pEW
  rw [show tensorWordDenAll e5pW = 512 by decide]
  norm_num

/-- The packed tensor of the target image over the width-64 literal source tensor. -/
def e5pXWL : List SVec := tensorPlanS 64 e5pPlanW twelfthX64

/-- The two descriptions of the target tensor agree. -/
theorem e5pXW_eqL : e5pXW = e5pXWL := by
  unfold e5pXW e5pXWL
  rw [twelfthX64_eq]

/-- The tensor bound of the literal description. -/
theorem e5pXWL_bnd : TBnd 64 (524288 * 15) e5pXWL := by
  rw [← e5pXW_eqL]
  exact e5pXW_bnd

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the source tensor. -/
theorem e5p_oddChkAh : OddDense.oddChk 64 (65536 * 10496 / 2 ^ 16) true false e5pTW
    (TSplit.thi 64 16 e5XH) (253952 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the source tensor. -/
theorem e5p_oddChkAl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e5pTW
    (TSplit.tlo 64 16 e5XH) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e5p_partA : oddWZ 64 true e5XH e5pVW = (16642998272 : ℤ) := by
  rw [TSplit.oddWZ_split 64 16 (by norm_num) true e5XH e5pVW,
    TSplit.oddWZ_of_chk2 true e5pVW e5pTW e5pVW_sh (TSplit.thi_bnd (by norm_num) e5XH_bnd) e5p_oddChkAh,
    TSplit.oddWZ_of_chk2 true e5pVW e5pTW e5pVW_sh (TSplit.tlo_bnd 64 16 (by norm_num) e5XH) e5p_oddChkAl]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the source against the tensor of the target. -/
theorem e5p_oddChkB : OddDense.oddChk 64 (524288 * 15) false true e5TH e5pXWL (33030144 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e5p_partB : oddLZ 64 true e5pXW e5VH = (33030144 : ℤ) := by
  rw [e5pXW_eqL, TSplit.oddLZ_of_chk2 true e5VH e5TH e5VH_sh e5pXWL_bnd e5p_oddChkB]

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e5p_tchk : TSplit.tdotSplitChk 64 16 (4 * (65536 * 10496)) (524288 * 15)
    (trialityTensorT 64 false e5XH) e5pXWL (4260607557632 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e5p_partC : tdot 64 (trialityTensorT 64 false e5XH) e5pXW = (4260607557632 : ℤ) := by
  rw [e5pXW_eqL, TSplit.tdot_of_splitChk (trialityTensorT_spec false e5XH_bnd (by norm_num)).1 e5pXWL_bnd e5p_tchk]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
