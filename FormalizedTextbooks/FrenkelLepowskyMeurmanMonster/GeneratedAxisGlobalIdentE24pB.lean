/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE24H
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE24pW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSplit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8MatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF

/-! # Dense identification E24+ (Sixth target): odd and tensor parts of the pairing

Pairing of the triality image (`fwd = true`) of `e24VH` (Eighth coset image) with `e24pVW` (Sixth image)
(`pairTriGZT`), each part one kernel check (values from a kernel evaluation). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor scale of the source side. -/
theorem e24p_EH : e24EH = 131072 := by
  unfold e24EH
  rw [show tensorWordDenAll e24H = 16 by decide, srcEighthH_den]
  norm_num

/-- The tensor scale of the target side. -/
theorem e24p_EW : e24pEW = 16384 := by
  unfold e24pEW
  rw [show tensorWordDenAll e24pW = 512 by decide]
  norm_num

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the target against the triality image of the source tensor. -/
theorem e24p_oddChkA : OddDense.oddChk 64 (256 * 10496) true false e24pTW e24XH (260046848 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the target against the triality image of the source tensor. -/
theorem e24p_partA : oddWZ 64 true e24XH e24pVW = (260046848 : ℤ) :=
  TSplit.oddWZ_of_chk2 true e24pVW e24pTW e24pVW_sh e24XH_bnd e24p_oddChkA

set_option maxRecDepth 100000 in
/-- Dense odd check: odd terms of the source against the tensor of the target. -/
theorem e24p_oddChkB : OddDense.oddChk 64 (524288 * (2 ^ 8 - 1)) false true e24TH e24pXW (31195136 : ℤ) = true := by
  decide +kernel

/-- The odd terms of the source against the tensor of the target. -/
theorem e24p_partB : oddLZ 64 true e24pXW e24VH = (31195136 : ℤ) := by
  rw [TSplit.oddLZ_of_chk2 true e24VH e24TH e24VH_sh e24pXW_bnd e24p_oddChkB]

set_option maxRecDepth 100000 in
/-- The split tensor dot product check. -/
theorem e24p_tchk : TSplit.tdotSplitChk 64 16 (4 * (256 * 10496)) (524288 * (2 ^ 8 - 1))
    (trialityTensorT 64 false e24XH) e24pXW (266287972352 : ℤ) = true := by
  decide +kernel

/-- The tensor part. -/
theorem e24p_partC : tdot 64 (trialityTensorT 64 false e24XH) e24pXW = (266287972352 : ℤ) := by
  rw [TSplit.tdot_of_splitChk (trialityTensorT_spec false e24XH_bnd (by norm_num)).1 e24pXW_bnd e24p_tchk]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
