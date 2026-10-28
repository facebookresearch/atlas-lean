/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE21H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE21xW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Dense identification E21+ (Seventh target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = true`) of `e21VH` (Eighth coset image) with `e21xVW` (Seventh image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e21x_EH : e21EH = 2097152 := by
  unfold e21EH
  rw [show tensorWordDenAll e21H = 256 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e21x_EW : e21xEW = 67108864 := by
  unfold e21xEW srcSeventhD0
  rw [show tensorWordDenAll e21xW = 8192 by decide, show tensorWordDenAll srcSeventhH = 4096 by decide]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the target against the triality image of the source tensor. -/
theorem e21x_oddChkA : OddDense.oddChk 64 (65536 * 10496) true false e21xTW e21XH (4244635648 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e21x_partA : oddWZ 64 true e21XH e21xVW = (4244635648 : ℤ) :=
  TSplit.oddWZ_of_chk2 true e21xVW e21xTW e21xVW_sh e21XH_bnd e21x_oddChkA

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e21x_oddChkBh : OddDense.oddChk 64 (274877906944 / 2 ^ 16) false true e21TH
    (TSplit.thi 64 16 e21xXW) (1990656 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e21x_oddChkBl : OddDense.oddChk 64 (2 ^ 16 - 1) false true e21TH
    (TSplit.tlo 64 16 e21xXW) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e21x_partB : oddLZ 64 true e21xXW e21VH = (130459631616 : ℤ) := by
  rw [TSplit.oddLZ_split 64 16 (by norm_num) true e21xXW e21VH,
    TSplit.oddLZ_of_chk2 true e21VH e21TH e21VH_sh (TSplit.thi_bnd (by norm_num) e21xXW_tight) e21x_oddChkBh,
    TSplit.oddLZ_of_chk2 true e21VH e21TH e21VH_sh (TSplit.tlo_bnd 64 16 (by norm_num) e21xXW) e21x_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e21x_tchk : TSplit.tdotSplitChk 64 16 (4 * (65536 * 10496)) (274877906944)
    (trialityTensorT 64 false e21XH) e21xXW (17099604835172352 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e21x_partC : tdot 64 (trialityTensorT 64 false e21XH) e21xXW = (17099604835172352 : ℤ) :=
  TSplit.tdot_of_splitChk (trialityTensorT_spec false e21XH_bnd (by norm_num)).1 e21xXW_tight e21x_tchk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
