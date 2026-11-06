/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC9pNTH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC9pNTG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (odd short terms, source tensor bound) of the identification Seventh cell record S7c9+
(gforest:S7c9+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c9pH_den : tensorWordDenAll s7c9pH = 4096 := by decide

set_option maxRecDepth 100000 in
/-- The odd short part of the pairing (normalized source tensor). -/
theorem s7c9p_hax : oddWZ 64 true s7c9pHXN s7c9pW = 260919263232 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 0..17. -/
theorem s7c9p_ha_s0 :
    selfOddB s7c9pW (ShortData.ofList s7c9pGT0).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT1).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT2).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT3).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT4).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT5).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT6).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT7).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT8).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT9).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT10).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT11).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT12).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT13).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT14).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT15).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT16).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT17).odd = 110784 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 18..35. -/
theorem s7c9p_ha_s1 :
    selfOddB s7c9pW (ShortData.ofList s7c9pGT18).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT19).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT20).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT21).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT22).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT23).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT24).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT25).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT26).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT27).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT28).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT29).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT30).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT31).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT32).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT33).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT34).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT35).odd = 89600 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 36..53. -/
theorem s7c9p_ha_s2 :
    selfOddB s7c9pW (ShortData.ofList s7c9pGT36).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT37).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT38).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT39).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT40).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT41).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT42).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT43).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT44).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT45).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT46).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT47).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT48).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT49).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT50).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT51).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT52).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT53).odd = 115456 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 54..71. -/
theorem s7c9p_ha_s3 :
    selfOddB s7c9pW (ShortData.ofList s7c9pGT54).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT55).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT56).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT57).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT58).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT59).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT60).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT61).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT62).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT63).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT64).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT65).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT66).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT67).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT68).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT69).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT70).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT71).odd = 74240 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 72..89. -/
theorem s7c9p_ha_s4 :
    selfOddB s7c9pW (ShortData.ofList s7c9pGT72).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT73).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT74).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT75).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT76).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT77).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT78).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT79).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT80).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT81).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT82).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT83).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT84).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT85).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT86).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT87).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT88).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT89).odd = 101888 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 90..91. -/
theorem s7c9p_ha_s5 :
    selfOddB s7c9pW (ShortData.ofList s7c9pGT90).odd +
    selfOddB s7c9pW (ShortData.ofList s7c9pGT91).odd = 5696 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the target fit the packed odd self sum. -/
theorem s7c9p_wodd : oddPackOk s7c9pW = true := by decide +kernel

/-- The odd self sum of the target. -/
theorem s7c9p_ha_s : selfOddP s7c9pW = 497664 := by
  rw [selfOddP_eq_B s7c9pW s7c9p_wodd]
  show selfOddB s7c9pW (ShortData.ofList s7c9pGT).odd = _
  simp only [s7c9pGT, ofList_odd_append, selfOddB_append]
  linarith [s7c9p_ha_s0, s7c9p_ha_s1, s7c9p_ha_s2, s7c9p_ha_s3, s7c9p_ha_s4, s7c9p_ha_s5]

/-- The odd short part equals the odd self part of the target. -/
theorem s7c9p_ha : (oddWZ 64 true s7c9pHXN s7c9pW : ℚ) / (2 * ((tensorWordDenAll s7c9pH : ℚ) *
    srcSeventhD0)) =
    s7c9pW.sden * (selfOddP s7c9pW : ℚ) := by
  rw [s7c9p_hax, s7c9p_ha_s]
  show ((260919263232 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c9pH : ℚ) * srcSeventhD0)) =
    1 / 128 * ((497664 : ℤ) : ℚ)
  rw [s7c9pH_den]
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
