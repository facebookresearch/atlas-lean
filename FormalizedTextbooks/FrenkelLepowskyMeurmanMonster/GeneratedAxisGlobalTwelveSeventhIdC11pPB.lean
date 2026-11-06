/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC11pLW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (octads) of the identification Seventh cell record S7c11+ (gforest:S7c11+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The octad part of the pairing over the target chunks 0..17. -/
theorem s7c11p_hn_n0 :
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT0).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT1).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT2).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT3).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT4).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT5).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT6).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT7).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT8).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT9).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT10).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT11).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT12).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT13).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT14).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT15).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT16).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT17).oct = 57671680 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad self part of the target over the target chunks 0..17. -/
theorem s7c11p_hn_s0 :
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT0).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT1).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT2).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT3).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT4).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT5).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT6).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT7).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT8).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT9).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT10).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT11).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT12).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT13).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT14).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT15).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT16).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT17).oct = 112640 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part of the pairing over the target chunks 18..35. -/
theorem s7c11p_hn_n1 :
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT18).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT19).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT20).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT21).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT22).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT23).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT24).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT25).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT26).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT27).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT28).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT29).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT30).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT31).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT32).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT33).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT34).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT35).oct = 50593792 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad self part of the target over the target chunks 18..35. -/
theorem s7c11p_hn_s1 :
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT18).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT19).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT20).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT21).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT22).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT23).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT24).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT25).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT26).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT27).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT28).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT29).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT30).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT31).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT32).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT33).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT34).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT35).oct = 98816 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part of the pairing over the target chunks 36..53. -/
theorem s7c11p_hn_n2 :
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT36).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT37).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT38).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT39).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT40).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT41).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT42).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT43).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT44).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT45).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT46).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT47).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT48).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT49).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT50).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT51).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT52).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT53).oct = 62357504 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad self part of the target over the target chunks 36..53. -/
theorem s7c11p_hn_s2 :
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT36).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT37).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT38).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT39).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT40).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT41).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT42).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT43).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT44).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT45).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT46).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT47).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT48).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT49).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT50).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT51).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT52).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT53).oct = 121792 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part of the pairing over the target chunks 54..71. -/
theorem s7c11p_hn_n3 :
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT54).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT55).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT56).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT57).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT58).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT59).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT60).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT61).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT62).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT63).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT64).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT65).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT66).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT67).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT68).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT69).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT70).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT71).oct = 37748736 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad self part of the target over the target chunks 54..71. -/
theorem s7c11p_hn_s3 :
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT54).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT55).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT56).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT57).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT58).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT59).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT60).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT61).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT62).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT63).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT64).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT65).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT66).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT67).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT68).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT69).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT70).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT71).oct = 73728 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part of the pairing over the target chunks 72..89. -/
theorem s7c11p_hn_n4 :
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT72).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT73).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT74).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT75).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT76).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT77).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT78).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT79).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT80).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT81).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT82).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT83).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT84).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT85).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT86).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT87).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT88).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT89).oct = 54525952 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad self part of the target over the target chunks 72..89. -/
theorem s7c11p_hn_s4 :
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT72).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT73).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT74).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT75).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT76).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT77).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT78).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT79).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT80).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT81).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT82).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT83).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT84).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT85).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT86).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT87).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT88).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT89).oct = 106496 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part of the pairing over the target chunks 90..91. -/
theorem s7c11p_hn_n5 :
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT90).oct +
    octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT91).oct = 2785280 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad self part of the target over the target chunks 90..91. -/
theorem s7c11p_hn_s5 :
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT90).oct +
    selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT91).oct = 5440 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the target fit the packed self sum of field width `48`. -/
theorem s7c11p_wok48 : octPackOk 48 s7c11pW = true := by decide +kernel

/-- The octad part of the pairing. -/
theorem s7c11p_hn_n : octSumZ 40 true s7c11pL s7c11pW = 265682944 := by
  rw [octSumZ_eq_B]
  show octSumB 40 true s7c11pL (ShortData.ofList s7c11pGT).oct = _
  simp only [s7c11pGT, ofList_oct_append, octSumB_append]
  linarith [s7c11p_hn_n0, s7c11p_hn_n1, s7c11p_hn_n2, s7c11p_hn_n3, s7c11p_hn_n4, s7c11p_hn_n5]

/-- The octad self sum of the target. -/
theorem s7c11p_hn_s : selfOctPW 48 s7c11pW = 518912 := by
  rw [selfOctPW_eq_B 48 s7c11pW s7c11p_wok48]
  show selfOctB 48 s7c11pW (ShortData.ofList s7c11pGT).oct = _
  simp only [s7c11pGT, ofList_oct_append, selfOctB_append]
  linarith [s7c11p_hn_s0, s7c11p_hn_s1, s7c11p_hn_s2, s7c11p_hn_s3, s7c11p_hn_s4, s7c11p_hn_s5]

/-- The octad part equals the octad self part of the target. -/
theorem s7c11p_hn : s7c11pL.sden * (octSumZ 40 true s7c11pL s7c11pW : ℚ) / 8 =
    s7c11pW.sden * (selfOctP s7c11pW : ℚ) := by
  rw [s7c11p_hn_n, selfOctP_eq, ← selfOctPW_eq 48, s7c11p_hn_s]
  show 1 / srcSeventhD0 * ((265682944 : ℤ) : ℚ) / 8 = 1 / 128 * ((518912 : ℤ) : ℚ)
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
