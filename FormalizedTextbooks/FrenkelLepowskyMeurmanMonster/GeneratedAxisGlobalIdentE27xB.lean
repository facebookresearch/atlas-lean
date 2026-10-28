/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE27H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE27xW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamFourth

/-! # Dense identification E27+ (Fourth target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = true`) of `e27VH` (Eighth coset image) with `e27xVW` (Fourth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e27x_EH : e27EH = 131072 := by
  unfold e27EH
  rw [show tensorWordDenAll e27H = 16 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e27x_EW : e27xEW = 512 := by
  unfold e27xEW
  rw [show tensorWordDenAll e27xW = 512 by decide]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the target against the triality image of the source tensor. -/
theorem e27x_oddChkA : OddDense.oddChk 64 (256 * 10496) true false e27xTW e27XH (71303168 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e27x_partA : oddWZ 64 true e27XH e27xVW = (71303168 : ℤ) :=
  TSplit.oddWZ_of_chk2 true e27xVW e27xTW e27xVW_sh e27XH_bnd e27x_oddChkA

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the source against the tensor of the target. -/
theorem e27x_oddChkB : OddDense.oddChk 64 (524288 * 56) false true e27TH e27xXW (917504 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e27x_partB : oddLZ 64 true e27xXW e27VH = (917504 : ℤ) :=
  TSplit.oddLZ_of_chk2 true e27VH e27TH e27VH_sh e27xXW_bnd e27x_oddChkB

set_option maxRecDepth 100000 in
/-- The multiplicative tensor dot product. -/
theorem e27x_tdotM : tdotM 64 (trialityTensorT 64 false e27XH) e27xXW = (7516192768 : ℤ) := by
  decide +kernel

/-- The tensor part. -/
theorem e27x_partC : tdot 64 (trialityTensorT 64 false e27XH) e27xXW = (7516192768 : ℤ) := by
  rw [← tdotM_eq (trialityTensorT_spec false e27XH_bnd (by norm_num)).1 e27xXW_bnd (by norm_num)]
  exact e27x_tdotM

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
