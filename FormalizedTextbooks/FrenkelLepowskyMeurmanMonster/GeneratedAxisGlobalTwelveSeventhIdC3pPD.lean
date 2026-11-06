/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3pNTH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3pNTG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (odd short terms, source tensor bound) of the identification Seventh cell record S7c3+
(gforest:S7c3+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c3pH_den : tensorWordDenAll s7c3pH = 256 := by decide

set_option maxRecDepth 100000 in
/-- The odd short part of the pairing (normalized source tensor). -/
theorem s7c3p_hax : oddWZ 64 true s7c3pHXN s7c3pW = 1929379840 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 0..8. -/
theorem s7c3p_ha_s0 :
    selfOddB s7c3pW (ShortData.ofList s7c3pGT0).odd +
    selfOddB s7c3pW (ShortData.ofList s7c3pGT1).odd +
    selfOddB s7c3pW (ShortData.ofList s7c3pGT2).odd +
    selfOddB s7c3pW (ShortData.ofList s7c3pGT3).odd +
    selfOddB s7c3pW (ShortData.ofList s7c3pGT4).odd +
    selfOddB s7c3pW (ShortData.ofList s7c3pGT5).odd +
    selfOddB s7c3pW (ShortData.ofList s7c3pGT6).odd +
    selfOddB s7c3pW (ShortData.ofList s7c3pGT7).odd +
    selfOddB s7c3pW (ShortData.ofList s7c3pGT8).odd = 7360 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the target fit the packed odd self sum. -/
theorem s7c3p_wodd : oddPackOk s7c3pW = true := by decide +kernel

/-- The odd self sum of the target. -/
theorem s7c3p_ha_s : selfOddP s7c3pW = 7360 := by
  rw [selfOddP_eq_B s7c3pW s7c3p_wodd]
  show selfOddB s7c3pW (ShortData.ofList s7c3pGT).odd = _
  simp only [s7c3pGT, ofList_odd_append, selfOddB_append]
  linarith [s7c3p_ha_s0]

/-- The odd short part equals the odd self part of the target. -/
theorem s7c3p_ha : (oddWZ 64 true s7c3pHXN s7c3pW : ℚ) / (2 * ((tensorWordDenAll s7c3pH : ℚ) *
    srcSeventhD0)) =
    s7c3pW.sden * (selfOddP s7c3pW : ℚ) := by
  rw [s7c3p_hax, s7c3p_ha_s]
  show ((1929379840 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c3pH : ℚ) * srcSeventhD0)) =
    1 / 16 * ((7360 : ℤ) : ℚ)
  rw [s7c3pH_den]
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
