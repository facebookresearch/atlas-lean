/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE3H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE3xW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF

/-! # Dense identification E3+ (Sixth target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = true`) of `e3VH` (Eighth coset image) with `e3xVW` (Sixth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e3x_EH : e3EH = 2097152 := by
  unfold e3EH
  rw [show tensorWordDenAll e3H = 256 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e3x_EW : e3xEW = 262144 := by
  unfold e3xEW
  rw [show tensorWordDenAll e3xW = 8192 by decide]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the target against the triality image of the source tensor. -/
theorem e3x_oddChkA : OddDense.oddChk 64 (65536 * 10496) true false e3xTW e3XH (4244635648 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e3x_partA : oddWZ 64 true e3XH e3xVW = (4244635648 : ℤ) :=
  TSplit.oddWZ_of_chk2 true e3xVW e3xTW e3xVW_sh e3XH_bnd e3x_oddChkA

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e3x_oddChkBh : OddDense.oddChk 64 (134217728 * (2 ^ 8 - 1) / 2 ^ 16) false true e3TH
    (TSplit.thi 64 16 e3xXW) (25504 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e3x_oddChkBl : OddDense.oddChk 64 (2 ^ 16 - 1) false true e3TH
    (TSplit.tlo 64 16 e3xXW) (-1161822208 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e3x_partB : oddLZ 64 true e3xXW e3VH = (509607936 : ℤ) := by
  rw [TSplit.oddLZ_split 64 16 (by norm_num) true e3xXW e3VH,
    TSplit.oddLZ_of_chk2 true e3VH e3TH e3VH_sh (TSplit.thi_bnd (by norm_num) e3xXW_bnd) e3x_oddChkBh,
    TSplit.oddLZ_of_chk2 true e3VH e3TH e3VH_sh (TSplit.tlo_bnd 64 16 (by norm_num) e3xXW) e3x_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e3x_tchk : TSplit.tdotSplitChk 64 16 (4 * (65536 * 10496)) (134217728 * (2 ^ 8 - 1))
    (trialityTensorT 64 false e3XH) e3xXW (66795331387392 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e3x_partC : tdot 64 (trialityTensorT 64 false e3XH) e3xXW = (66795331387392 : ℤ) :=
  TSplit.tdot_of_splitChk (trialityTensorT_spec false e3XH_bnd (by norm_num)).1 e3xXW_bnd e3x_tchk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
