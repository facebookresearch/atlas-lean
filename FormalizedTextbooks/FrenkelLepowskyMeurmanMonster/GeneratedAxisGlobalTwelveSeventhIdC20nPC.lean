/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC20nLW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (tensor) of the identification Seventh cell record S7c20- (gforest:S7c20-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c20nH_denC : tensorWordDenAll s7c20nH = 256 := by decide

/-- The tensor denominator of the target word. -/
theorem s7c20nG_den : tensorWordDenAll s7c20nG = 512 := by decide

set_option maxRecDepth 100000 in
/-- The odd short terms of the source against the target tensor, the self dot of the target tensor,
and the fields of the target tensor are below `2^31` (one kernel evaluation of the target
tensor). -/
theorem s7c20n_hty : oddLZ 80 false s7c20nGX s7c20nL = 1924145348608 ∧ tdotM 80 s7c20nGX s7c20nGX
    = 2137450604396544 ∧
    colsLtB 80 31 s7c20nGX = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem s7c20n_htc : tdotM 80 (trialityTensorT 80 (!false) s7c20nHX) s7c20nGX = 1152288185909248
    := by
  decide +kernel

/-- The tensor part equals the tensor self part of the target. -/
theorem s7c20n_ht : s7c20nL.sden * (oddLZ 80 false s7c20nGX s7c20nL : ℚ) / ((tensorWordDenAll
    s7c20nG : ℚ) * srcSeventhD0) +
    (tdotM 80 (trialityTensorT 80 (!false) s7c20nHX) s7c20nGX : ℚ) / (2 * ((tensorWordDenAll
        s7c20nH : ℚ) * srcSeventhD0) * ((tensorWordDenAll s7c20nG : ℚ) * srcSeventhD0)) =
      (tdotM 80 s7c20nGX s7c20nGX : ℚ) / (((tensorWordDenAll s7c20nG : ℚ) * srcSeventhD0) *
          ((tensorWordDenAll s7c20nG : ℚ) * srcSeventhD0)) := by
  rw [s7c20n_hty.1, s7c20n_hty.2.1, s7c20n_htc]
  show 1 / srcSeventhD0 * ((1924145348608 : ℤ) : ℚ) / ((tensorWordDenAll s7c20nG : ℚ) *
      srcSeventhD0) +
      ((1152288185909248 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c20nH : ℚ) * srcSeventhD0) *
        ((tensorWordDenAll s7c20nG : ℚ) * srcSeventhD0)) =
      ((2137450604396544 : ℤ) : ℚ) / (((tensorWordDenAll s7c20nG : ℚ) * srcSeventhD0) *
        ((tensorWordDenAll s7c20nG : ℚ) * srcSeventhD0))
  rw [s7c20nH_denC, s7c20nG_den]
  norm_num [srcSeventhD0_eq]

/-- The fields of the target tensor are below `2^31`. -/
theorem s7c20n_ylt : colsLtB 80 31 s7c20nGX = true := s7c20n_hty.2.2

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
