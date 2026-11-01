/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC1nNTH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC1nNTG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (tensor) of the identification Seventh cell record S7c1- (gforest:S7c1-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c1nH_denC : tensorWordDenAll s7c1nH = 256 := by decide

/-- The tensor denominator of the target word. -/
theorem s7c1nG_den : tensorWordDenAll s7c1nG = 512 := by decide

set_option maxRecDepth 100000 in
/-- The odd short terms of the source against the target tensor, the self dot of the target tensor,
and the fields of the target tensor are below `2^20` (one kernel evaluation of the target
tensor). -/
theorem s7c1n_hty : oddLZ 64 false s7c1nGXN s7c1nL = 2130303778816 ∧ tdotM 64 s7c1nGXN s7c1nGXN =
    2137450604396544 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem s7c1n_htc : tdotM 64 (trialityTensorT 64 (!false) s7c1nHXN) s7c1nGXN = 1046735069642752 :=
    by
  decide +kernel

/-- The tensor part equals the tensor self part of the target. -/
theorem s7c1n_ht : s7c1nL.sden * (oddLZ 64 false s7c1nGXN s7c1nL : ℚ) / ((tensorWordDenAll s7c1nG
    : ℚ) * srcSeventhD0) +
    (tdotM 64 (trialityTensorT 64 (!false) s7c1nHXN) s7c1nGXN : ℚ) / (2 * ((tensorWordDenAll
        s7c1nH : ℚ) * srcSeventhD0) * ((tensorWordDenAll s7c1nG : ℚ) * srcSeventhD0)) =
      (tdotM 64 s7c1nGXN s7c1nGXN : ℚ) / (((tensorWordDenAll s7c1nG : ℚ) * srcSeventhD0) *
          ((tensorWordDenAll s7c1nG : ℚ) * srcSeventhD0)) := by
  rw [s7c1n_hty.1, s7c1n_hty.2, s7c1n_htc]
  show 1 / srcSeventhD0 * ((2130303778816 : ℤ) : ℚ) / ((tensorWordDenAll s7c1nG : ℚ) *
      srcSeventhD0) +
      ((1046735069642752 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c1nH : ℚ) * srcSeventhD0) *
        ((tensorWordDenAll s7c1nG : ℚ) * srcSeventhD0)) =
      ((2137450604396544 : ℤ) : ℚ) / (((tensorWordDenAll s7c1nG : ℚ) * srcSeventhD0) *
        ((tensorWordDenAll s7c1nG : ℚ) * srcSeventhD0))
  rw [s7c1nH_denC, s7c1nG_den]
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
