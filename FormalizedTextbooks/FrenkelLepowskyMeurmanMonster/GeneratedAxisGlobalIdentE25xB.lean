/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE25H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE25xW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ

/-! # Dense identification E25- (Fifth target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = false`) of `e25VH` (Eighth coset image) with `e25xVW` (Fifth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e25x_EH : e25EH = 131072 := by
  unfold e25EH
  rw [show tensorWordDenAll e25H = 16 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e25x_EW : e25xEW = 512 := by
  unfold e25xEW
  rw [show tensorWordDenAll e25xW = 512 by decide]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the target against the triality image of the source tensor. -/
theorem e25x_oddChkA : OddDense.oddChk 64 (256 * 10496) false true e25xTW e25XH (125829120 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e25x_partA : oddWZ 64 false e25XH e25xVW = (125829120 : ℤ) :=
  TSplit.oddWZ_of_chk2 false e25xVW e25xTW e25xVW_sh e25XH_bnd e25x_oddChkA

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the source against the tensor of the target. -/
theorem e25x_oddChkB : OddDense.oddChk 64 (524288 * 64) true false e25TH e25xXW (1048576 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e25x_partB : oddLZ 64 false e25xXW e25VH = (1048576 : ℤ) :=
  TSplit.oddLZ_of_chk2 false e25VH e25TH e25VH_sh e25xXW_bnd e25x_oddChkB

set_option maxRecDepth 100000 in
/-- The multiplicative tensor dot product. -/
theorem e25x_tdotM : tdotM 64 (trialityTensorT 64 true e25XH) e25xXW = (8589934592 : ℤ) := by
  decide +kernel

/-- The tensor part. -/
theorem e25x_partC : tdot 64 (trialityTensorT 64 true e25XH) e25xXW = (8589934592 : ℤ) := by
  rw [← tdotM_eq (trialityTensorT_spec true e25XH_bnd (by norm_num)).1 e25xXW_bnd (by norm_num)]
  exact e25x_tdotM

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
