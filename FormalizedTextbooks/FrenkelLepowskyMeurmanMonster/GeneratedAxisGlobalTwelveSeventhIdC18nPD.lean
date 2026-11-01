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

/-! # Parts (odd short terms, source tensor bound) of the identification Seventh cell record
S7c18- (gforest:S7c18-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c18nH_den : tensorWordDenAll s7c18nH = 256 := by decide

set_option maxRecDepth 100000 in
/-- The odd short part of the pairing, and the fields of the source tensor are below `2^28`
(one kernel evaluation of the source tensor). -/
theorem s7c18n_hax : oddWZ 72 false s7c18nHX s7c18nW = 962072674304 ∧ colsLtB 72 28 s7c18nHX =
    true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 0..17. -/
theorem s7c18n_ha_s0 :
    selfOddB s7c18nW (ShortData.ofList s7c18nGT0).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT1).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT2).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT3).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT4).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT5).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT6).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT7).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT8).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT9).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT10).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT11).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT12).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT13).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT14).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT15).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT16).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT17).odd = 490733568 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 18..35. -/
theorem s7c18n_ha_s1 :
    selfOddB s7c18nW (ShortData.ofList s7c18nGT18).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT19).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT20).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT21).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT22).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT23).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT24).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT25).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT26).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT27).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT28).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT29).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT30).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT31).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT32).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT33).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT34).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT35).odd = 415760384 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 36..53. -/
theorem s7c18n_ha_s2 :
    selfOddB s7c18nW (ShortData.ofList s7c18nGT36).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT37).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT38).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT39).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT40).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT41).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT42).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT43).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT44).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT45).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT46).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT47).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT48).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT49).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT50).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT51).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT52).odd +
    selfOddB s7c18nW (ShortData.ofList s7c18nGT53).odd = 972554240 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the target fit the packed odd self sum. -/
theorem s7c18n_wodd : oddPackOk s7c18nW = true := by decide +kernel

/-- The odd self sum of the target. -/
theorem s7c18n_ha_s : selfOddP s7c18nW = 1879048192 := by
  rw [selfOddP_eq_B s7c18nW s7c18n_wodd]
  show selfOddB s7c18nW (ShortData.ofList s7c18nGT).odd = _
  simp only [s7c18nGT, ofList_odd_append, selfOddB_append]
  linarith [s7c18n_ha_s0, s7c18n_ha_s1, s7c18n_ha_s2]

/-- The odd short part equals the odd self part of the target. -/
theorem s7c18n_ha : (oddWZ 72 false s7c18nHX s7c18nW : ℚ) / (2 * ((tensorWordDenAll s7c18nH : ℚ) *
    srcSeventhD0)) =
    s7c18nW.sden * (selfOddP s7c18nW : ℚ) := by
  rw [s7c18n_hax.1, s7c18n_ha_s]
  show ((962072674304 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c18nH : ℚ) * srcSeventhD0)) =
    1 / srcSeventhD0 * ((1879048192 : ℤ) : ℚ)
  rw [srcSeventhD0_eq, s7c18nH_den]
  norm_num

/-- The fields of the source tensor are below `2^28`. -/
theorem s7c18n_xlt : colsLtB 72 28 s7c18nHX = true := s7c18n_hax.2

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
