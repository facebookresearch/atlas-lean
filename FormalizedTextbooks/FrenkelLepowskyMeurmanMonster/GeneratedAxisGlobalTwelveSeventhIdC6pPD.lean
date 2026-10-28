/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC6pNTH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC6pNTG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (odd short terms, source tensor bound) of the identification Seventh cell record S7c6+
(gforest:S7c6+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c6pH_den : tensorWordDenAll s7c6pH = 4096 := by decide

set_option maxRecDepth 100000 in
/-- The odd short part of the pairing (normalized source tensor). -/
theorem s7c6p_hax : oddWZ 64 true s7c6pHXN s7c6pW = 260919263232 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 0..17. -/
theorem s7c6p_ha_s0 :
    selfOddB s7c6pW (ShortData.ofList s7c6pGT0).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT1).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT2).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT3).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT4).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT5).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT6).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT7).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT8).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT9).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT10).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT11).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT12).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT13).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT14).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT15).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT16).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT17).odd = 103616 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 18..35. -/
theorem s7c6p_ha_s1 :
    selfOddB s7c6pW (ShortData.ofList s7c6pGT18).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT19).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT20).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT21).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT22).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT23).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT24).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT25).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT26).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT27).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT28).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT29).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT30).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT31).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT32).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT33).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT34).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT35).odd = 97280 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 36..53. -/
theorem s7c6p_ha_s2 :
    selfOddB s7c6pW (ShortData.ofList s7c6pGT36).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT37).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT38).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT39).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT40).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT41).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT42).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT43).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT44).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT45).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT46).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT47).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT48).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT49).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT50).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT51).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT52).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT53).odd = 111168 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 54..71. -/
theorem s7c6p_ha_s3 :
    selfOddB s7c6pW (ShortData.ofList s7c6pGT54).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT55).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT56).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT57).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT58).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT59).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT60).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT61).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT62).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT63).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT64).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT65).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT66).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT67).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT68).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT69).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT70).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT71).odd = 76416 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 72..89. -/
theorem s7c6p_ha_s4 :
    selfOddB s7c6pW (ShortData.ofList s7c6pGT72).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT73).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT74).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT75).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT76).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT77).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT78).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT79).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT80).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT81).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT82).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT83).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT84).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT85).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT86).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT87).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT88).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT89).odd = 104192 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 90..91. -/
theorem s7c6p_ha_s5 :
    selfOddB s7c6pW (ShortData.ofList s7c6pGT90).odd +
    selfOddB s7c6pW (ShortData.ofList s7c6pGT91).odd = 4992 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the target fit the packed odd self sum. -/
theorem s7c6p_wodd : oddPackOk s7c6pW = true := by decide +kernel

/-- The odd self sum of the target. -/
theorem s7c6p_ha_s : selfOddP s7c6pW = 497664 := by
  rw [selfOddP_eq_B s7c6pW s7c6p_wodd]
  show selfOddB s7c6pW (ShortData.ofList s7c6pGT).odd = _
  simp only [s7c6pGT, ofList_odd_append, selfOddB_append]
  linarith [s7c6p_ha_s0, s7c6p_ha_s1, s7c6p_ha_s2, s7c6p_ha_s3, s7c6p_ha_s4, s7c6p_ha_s5]

/-- The odd short part equals the odd self part of the target. -/
theorem s7c6p_ha : (oddWZ 64 true s7c6pHXN s7c6pW : ℚ) / (2 * ((tensorWordDenAll s7c6pH : ℚ) *
    srcSeventhD0)) =
    s7c6pW.sden * (selfOddP s7c6pW : ℚ) := by
  rw [s7c6p_hax, s7c6p_ha_s]
  show ((260919263232 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c6pH : ℚ) * srcSeventhD0)) =
    1 / 128 * ((497664 : ℤ) : ℚ)
  rw [s7c6pH_den]
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
