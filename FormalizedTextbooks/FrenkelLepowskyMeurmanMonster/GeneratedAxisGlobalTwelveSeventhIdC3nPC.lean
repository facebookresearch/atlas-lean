/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3nLW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (tensor) of the identification Seventh cell record S7c3- (gforest:S7c3-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c3nH_denC : tensorWordDenAll s7c3nH = 256 := by decide

/-- The tensor denominator of the target word. -/
theorem s7c3nG_den : tensorWordDenAll s7c3nG = 512 := by decide

set_option maxRecDepth 100000 in
/-- The odd short terms of the source against the target tensor, the self dot of the target tensor,
and the fields of the target tensor are below `2^31` (one kernel evaluation of the target
tensor). -/
theorem s7c3n_hty : oddLZ 80 false s7c3nGX s7c3nL = 2199023255552 ∧ tdotM 80 s7c3nGX s7c3nGX =
    2137450604396544 ∧
    colsLtB 80 31 s7c3nGX = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem s7c3n_htc : tdotM 80 (trialityTensorT 80 (!false) s7c3nHX) s7c3nGX = 1011550697553920 := by
  decide +kernel

/-- The tensor part equals the tensor self part of the target. -/
theorem s7c3n_ht : s7c3nL.sden * (oddLZ 80 false s7c3nGX s7c3nL : ℚ) / ((tensorWordDenAll s7c3nG :
    ℚ) * srcSeventhD0) +
    (tdotM 80 (trialityTensorT 80 (!false) s7c3nHX) s7c3nGX : ℚ) / (2 * ((tensorWordDenAll s7c3nH
        : ℚ) * srcSeventhD0) * ((tensorWordDenAll s7c3nG : ℚ) * srcSeventhD0)) =
      (tdotM 80 s7c3nGX s7c3nGX : ℚ) / (((tensorWordDenAll s7c3nG : ℚ) * srcSeventhD0) *
          ((tensorWordDenAll s7c3nG : ℚ) * srcSeventhD0)) := by
  rw [s7c3n_hty.1, s7c3n_hty.2.1, s7c3n_htc]
  show 1 / srcSeventhD0 * ((2199023255552 : ℤ) : ℚ) / ((tensorWordDenAll s7c3nG : ℚ) *
      srcSeventhD0) +
      ((1011550697553920 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c3nH : ℚ) * srcSeventhD0) *
        ((tensorWordDenAll s7c3nG : ℚ) * srcSeventhD0)) =
      ((2137450604396544 : ℤ) : ℚ) / (((tensorWordDenAll s7c3nG : ℚ) * srcSeventhD0) *
        ((tensorWordDenAll s7c3nG : ℚ) * srcSeventhD0))
  rw [srcSeventhD0_eq, s7c3nH_denC, s7c3nG_den]
  norm_num

/-- The fields of the target tensor are below `2^31`. -/
theorem s7c3n_ylt : colsLtB 80 31 s7c3nGX = true := s7c3n_hty.2.2

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
