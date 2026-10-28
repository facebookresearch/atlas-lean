/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3nLW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (odd short terms, source tensor bound) of the identification Seventh cell record S7c3-
(gforest:S7c3-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c3nH_den : tensorWordDenAll s7c3nH = 256 := by decide

set_option maxRecDepth 100000 in
/-- The odd short part of the pairing, and the fields of the source tensor are below `2^29`
(one kernel evaluation of the source tensor). -/
theorem s7c3n_hax : oddWZ 80 false s7c3nHX s7c3nW = 1099511627776 ∧ colsLtB 80 29 s7c3nHX = true
    := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 0..8. -/
theorem s7c3n_ha_s0 :
    selfOddB s7c3nW (ShortData.ofList s7c3nGT0).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT1).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT2).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT3).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT4).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT5).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT6).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT7).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT8).odd = 278396928 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 9..17. -/
theorem s7c3n_ha_s1 :
    selfOddB s7c3nW (ShortData.ofList s7c3nGT9).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT10).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT11).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT12).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT13).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT14).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT15).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT16).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT17).odd = 411041792 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 18..26. -/
theorem s7c3n_ha_s2 :
    selfOddB s7c3nW (ShortData.ofList s7c3nGT18).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT19).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT20).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT21).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT22).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT23).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT24).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT25).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT26).odd = 279445504 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 27..35. -/
theorem s7c3n_ha_s3 :
    selfOddB s7c3nW (ShortData.ofList s7c3nGT27).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT28).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT29).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT30).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT31).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT32).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT33).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT34).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT35).odd = 206307328 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 36..44. -/
theorem s7c3n_ha_s4 :
    selfOddB s7c3nW (ShortData.ofList s7c3nGT36).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT37).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT38).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT39).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT40).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT41).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT42).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT43).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT44).odd = 559939584 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd self part of the target over the target chunks 45..53. -/
theorem s7c3n_ha_s5 :
    selfOddB s7c3nW (ShortData.ofList s7c3nGT45).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT46).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT47).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT48).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT49).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT50).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT51).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT52).odd +
    selfOddB s7c3nW (ShortData.ofList s7c3nGT53).odd = 412352512 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the target fit the packed odd self sum. -/
theorem s7c3n_wodd : oddPackOk s7c3nW = true := by decide +kernel

/-- The odd self sum of the target. -/
theorem s7c3n_ha_s : selfOddP s7c3nW = 2147483648 := by
  rw [selfOddP_eq_B s7c3nW s7c3n_wodd]
  show selfOddB s7c3nW (ShortData.ofList s7c3nGT).odd = _
  simp only [s7c3nGT, ofList_odd_append, selfOddB_append]
  linarith [s7c3n_ha_s0, s7c3n_ha_s1, s7c3n_ha_s2, s7c3n_ha_s3, s7c3n_ha_s4, s7c3n_ha_s5]

/-- The odd short part equals the odd self part of the target. -/
theorem s7c3n_ha : (oddWZ 80 false s7c3nHX s7c3nW : ℚ) / (2 * ((tensorWordDenAll s7c3nH : ℚ) *
    srcSeventhD0)) =
    s7c3nW.sden * (selfOddP s7c3nW : ℚ) := by
  rw [s7c3n_hax.1, s7c3n_ha_s]
  show ((1099511627776 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c3nH : ℚ) * srcSeventhD0)) =
    1 / srcSeventhD0 * ((2147483648 : ℤ) : ℚ)
  rw [srcSeventhD0_eq, s7c3nH_den]
  norm_num

/-- The fields of the source tensor are below `2^29`. -/
theorem s7c3n_xlt : colsLtB 80 29 s7c3nHX = true := s7c3n_hax.2

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
