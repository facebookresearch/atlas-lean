/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE12H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE12xW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Dense identification E12- (Tenth target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = false`) of `e12VH` (Eighth coset image) with `e12xVW` (Tenth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e12x_EH : e12EH = 2097152 := by
  unfold e12EH
  rw [show tensorWordDenAll e12H = 256 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e12x_EW : e12xEW = 4194304 := by
  unfold e12xEW
  rw [show tensorWordDenAll e12xW = 131072 by decide]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the source tensor. -/
theorem e12x_oddChkAh : OddDense.oddChk 64 (65536 * 10496 / 2 ^ 16) false true e12xTW
    (TSplit.thi 64 16 e12XH) (250880 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the source tensor. -/
theorem e12x_oddChkAl : OddDense.oddChk 64 (2 ^ 16 - 1) false true e12xTW
    (TSplit.tlo 64 16 e12XH) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e12x_partA : oddWZ 64 false e12XH e12xVW = (16441671680 : ℤ) := by
  rw [TSplit.oddWZ_split 64 16 (by norm_num) false e12XH e12xVW,
    TSplit.oddWZ_of_chk2 false e12xVW e12xTW e12xVW_sh (TSplit.thi_bnd (by norm_num) e12XH_bnd) e12x_oddChkAh,
    TSplit.oddWZ_of_chk2 false e12xVW e12xTW e12xVW_sh (TSplit.tlo_bnd 64 16 (by norm_num) e12XH) e12x_oddChkAl]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check, high part of the target tensor. -/
theorem e12x_oddChkBh : OddDense.oddChk 64 (34359738368 * 15 / 2 ^ 16) true false e12TH
    (TSplit.thi 64 16 e12xXW) (128512 : ℤ) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Dense odd check, low part of the target tensor. -/
theorem e12x_oddChkBl : OddDense.oddChk 64 (2 ^ 16 - 1) true false e12TH
    (TSplit.tlo 64 16 e12xXW) (0 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e12x_partB : oddLZ 64 false e12xXW e12VH = (8422162432 : ℤ) := by
  rw [TSplit.oddLZ_split 64 16 (by norm_num) false e12xXW e12VH,
    TSplit.oddLZ_of_chk2 false e12VH e12TH e12VH_sh (TSplit.thi_bnd (by norm_num) e12xXW_bnd) e12x_oddChkBh,
    TSplit.oddLZ_of_chk2 false e12VH e12TH e12VH_sh (TSplit.tlo_bnd 64 16 (by norm_num) e12xXW) e12x_oddChkBl]
  norm_num

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e12x_tchk : TSplit.tdotSplitChk 64 16 (4 * (65536 * 10496)) (34359738368 * 15)
    (trialityTensorT 64 true e12XH) e12xXW (1103909674287104 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e12x_partC : tdot 64 (trialityTensorT 64 true e12XH) e12xXW = (1103909674287104 : ℤ) :=
  TSplit.tdot_of_splitChk (trialityTensorT_spec true e12XH_bnd (by norm_num)).1 e12xXW_bnd e12x_tchk

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
