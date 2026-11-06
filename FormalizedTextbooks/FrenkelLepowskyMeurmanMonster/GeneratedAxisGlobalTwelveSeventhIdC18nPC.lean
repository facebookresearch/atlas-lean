/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC18nLW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (tensor) of the identification Seventh cell record S7c18- (gforest:S7c18-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c18nH_denC : tensorWordDenAll s7c18nH = 256 := by decide

/-- The tensor denominator of the target word. -/
theorem s7c18nG_den : tensorWordDenAll s7c18nG = 256 := by decide

set_option maxRecDepth 100000 in
/-- The odd short terms of the source against the target tensor, the self dot of the target tensor,
and the fields of the target tensor are below `2^28` (one kernel evaluation of the target
tensor). -/
theorem s7c18n_hty : oddLZ 72 false s7c18nGX s7c18nL = 962072674304 ∧ tdotM 72 s7c18nGX s7c18nGX =
    534362651099136 ∧
    colsLtB 72 28 s7c18nGX = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem s7c18n_htc : tdotM 72 (trialityTensorT 72 (!false) s7c18nHX) s7c18nGX = 576144092954624 :=
    by
  decide +kernel

/-- The tensor part equals the tensor self part of the target. -/
theorem s7c18n_ht : s7c18nL.sden * (oddLZ 72 false s7c18nGX s7c18nL : ℚ) / ((tensorWordDenAll
    s7c18nG : ℚ) * srcSeventhD0) +
    (tdotM 72 (trialityTensorT 72 (!false) s7c18nHX) s7c18nGX : ℚ) / (2 * ((tensorWordDenAll
        s7c18nH : ℚ) * srcSeventhD0) * ((tensorWordDenAll s7c18nG : ℚ) * srcSeventhD0)) =
      (tdotM 72 s7c18nGX s7c18nGX : ℚ) / (((tensorWordDenAll s7c18nG : ℚ) * srcSeventhD0) *
          ((tensorWordDenAll s7c18nG : ℚ) * srcSeventhD0)) := by
  rw [s7c18n_hty.1, s7c18n_hty.2.1, s7c18n_htc]
  show 1 / srcSeventhD0 * ((962072674304 : ℤ) : ℚ) / ((tensorWordDenAll s7c18nG : ℚ) *
      srcSeventhD0) +
      ((576144092954624 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c18nH : ℚ) * srcSeventhD0) *
        ((tensorWordDenAll s7c18nG : ℚ) * srcSeventhD0)) =
      ((534362651099136 : ℤ) : ℚ) / (((tensorWordDenAll s7c18nG : ℚ) * srcSeventhD0) *
        ((tensorWordDenAll s7c18nG : ℚ) * srcSeventhD0))
  rw [srcSeventhD0_eq, s7c18nH_denC, s7c18nG_den]
  norm_num

/-- The fields of the target tensor are below `2^28`. -/
theorem s7c18n_ylt : colsLtB 72 28 s7c18nGX = true := s7c18n_hty.2.2

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
