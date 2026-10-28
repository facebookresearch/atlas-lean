/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC6pNTH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC6pNTG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (odd short terms, source tensor bound) of the identification Sixth cell record S6c6+
(gforest:S6c6+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s6c6pH_den : tensorWordDenAll s6c6pH = 65536 := by decide

set_option maxRecDepth 100000 in
/-- The odd short part of the pairing (normalized source tensor). -/
theorem s6c6p_hax : oddWZ 64 true s6c6pHXN s6c6pW = 4076863488 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 0..17. -/
theorem s6c6p_ha_s0 :
    selfOddB s6c6pW (ShortData.ofList s6c6pGT0).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT1).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT2).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT3).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT4).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT5).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT6).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT7).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT8).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT9).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT10).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT11).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT12).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT13).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT14).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT15).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT16).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT17).odd = 10892 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 18..35. -/
theorem s6c6p_ha_s1 :
    selfOddB s6c6pW (ShortData.ofList s6c6pGT18).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT19).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT20).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT21).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT22).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT23).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT24).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT25).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT26).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT27).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT28).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT29).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT30).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT31).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT32).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT33).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT34).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT35).odd = 4364 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 36..53. -/
theorem s6c6p_ha_s2 :
    selfOddB s6c6pW (ShortData.ofList s6c6pGT36).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT37).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT38).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT39).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT40).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT41).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT42).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT43).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT44).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT45).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT46).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT47).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT48).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT49).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT50).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT51).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT52).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT53).odd = 12304 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 54..59. -/
theorem s6c6p_ha_s3 :
    selfOddB s6c6pW (ShortData.ofList s6c6pGT54).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT55).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT56).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT57).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT58).odd +
    selfOddB s6c6pW (ShortData.ofList s6c6pGT59).odd = 3544 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the target fit the packed odd self sum. -/
theorem s6c6p_wodd : oddPackOk s6c6pW = true := by decide +kernel

/-- The odd self sum of the target. -/
theorem s6c6p_ha_s : selfOddP s6c6pW = 31104 := by
  rw [selfOddP_eq_B s6c6pW s6c6p_wodd]
  show selfOddB s6c6pW (ShortData.ofList s6c6pGT).odd = _
  simp only [s6c6pGT, ofList_odd_append, selfOddB_append]
  linarith [s6c6p_ha_s0, s6c6p_ha_s1, s6c6p_ha_s2, s6c6p_ha_s3]

/-- The odd short part equals the odd self part of the target. -/
theorem s6c6p_ha : (oddWZ 64 true s6c6pHXN s6c6pW : ℚ) / (2 * ((tensorWordDenAll s6c6pH : ℚ) *
    32)) =
    s6c6pW.sden * (selfOddP s6c6pW : ℚ) := by
  rw [s6c6p_hax, s6c6p_ha_s]
  show ((4076863488 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s6c6pH : ℚ) * 32)) =
    1 / 32 * ((31104 : ℤ) : ℚ)
  rw [s6c6pH_den]
  norm_num

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
