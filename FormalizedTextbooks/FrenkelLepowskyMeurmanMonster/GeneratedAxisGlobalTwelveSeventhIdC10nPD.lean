/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10nNTH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10nNTG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (odd short terms, source tensor bound) of the identification Seventh cell record
S7c10- (gforest:S7c10-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c10nH_den : tensorWordDenAll s7c10nH = 4096 := by decide

set_option maxRecDepth 100000 in
/-- The odd short part of the pairing (normalized source tensor). -/
theorem s7c10n_hax : oddWZ 64 false s7c10nHXN s7c10nW = 253403070464 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 0..17. -/
theorem s7c10n_ha_s0 :
    selfOddB s7c10nW (ShortData.ofList s7c10nGT0).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT1).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT2).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT3).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT4).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT5).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT6).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT7).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT8).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT9).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT10).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT11).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT12).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT13).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT14).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT15).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT16).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT17).odd = 121856 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 18..35. -/
theorem s7c10n_ha_s1 :
    selfOddB s7c10nW (ShortData.ofList s7c10nGT18).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT19).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT20).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT21).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT22).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT23).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT24).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT25).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT26).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT27).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT28).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT29).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT30).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT31).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT32).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT33).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT34).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT35).odd = 118784 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 36..53. -/
theorem s7c10n_ha_s2 :
    selfOddB s7c10nW (ShortData.ofList s7c10nGT36).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT37).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT38).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT39).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT40).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT41).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT42).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT43).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT44).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT45).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT46).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT47).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT48).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT49).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT50).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT51).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT52).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT53).odd = 138896 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 54..65. -/
theorem s7c10n_ha_s3 :
    selfOddB s7c10nW (ShortData.ofList s7c10nGT54).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT55).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT56).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT57).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT58).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT59).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT60).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT61).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT62).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT63).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT64).odd +
    selfOddB s7c10nW (ShortData.ofList s7c10nGT65).odd = 103792 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the target fit the packed odd self sum. -/
theorem s7c10n_wodd : oddPackOk s7c10nW = true := by decide +kernel

/-- The odd self sum of the target. -/
theorem s7c10n_ha_s : selfOddP s7c10nW = 483328 := by
  rw [selfOddP_eq_B s7c10nW s7c10n_wodd]
  show selfOddB s7c10nW (ShortData.ofList s7c10nGT).odd = _
  simp only [s7c10nGT, ofList_odd_append, selfOddB_append]
  linarith [s7c10n_ha_s0, s7c10n_ha_s1, s7c10n_ha_s2, s7c10n_ha_s3]

/-- The odd short part equals the odd self part of the target. -/
theorem s7c10n_ha : (oddWZ 64 false s7c10nHXN s7c10nW : ℚ) / (2 * ((tensorWordDenAll s7c10nH : ℚ)
    * srcSeventhD0)) =
    s7c10nW.sden * (selfOddP s7c10nW : ℚ) := by
  rw [s7c10n_hax, s7c10n_ha_s]
  show ((253403070464 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c10nH : ℚ) * srcSeventhD0)) =
    1 / 128 * ((483328 : ℤ) : ℚ)
  rw [s7c10nH_den]
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
