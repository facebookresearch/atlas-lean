/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC6pLW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixth

/-! # Parts (octad check, matrix, pairs) of the identification Sixth cell record S6c6+
(gforest:S6c6+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem s6c6p_hok : octPackOk 40 s6c6pL = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 0..17. -/
theorem s6c6p_hm_g0 :
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT0).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT1).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT2).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT3).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT4).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT5).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT6).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT7).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT8).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT9).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT10).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT11).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT12).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT13).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT14).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT15).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT16).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT17).pairs = 32640 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 18..35. -/
theorem s6c6p_hm_g1 :
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT18).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT19).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT20).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT21).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT22).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT23).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT24).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT25).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT26).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT27).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT28).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT29).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT30).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT31).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT32).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT33).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT34).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT35).pairs = 4096 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 36..53. -/
theorem s6c6p_hm_g2 :
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT36).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT37).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT38).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT39).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT40).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT41).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT42).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT43).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT44).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT45).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT46).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT47).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT48).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT49).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT50).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT51).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT52).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT53).pairs = 12800 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 54..59. -/
theorem s6c6p_hm_g3 :
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT54).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT55).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT56).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT57).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT58).pairs +
    triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT59).pairs = 5120 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 0..17. -/
theorem s6c6p_hp_g0 :
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT0).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT1).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT2).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT3).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT4).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT5).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT6).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT7).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT8).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT9).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT10).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT11).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT12).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT13).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT14).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT15).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT16).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT17).pairs = (255 : ℚ)
        / 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 0..17. -/
theorem s6c6p_sp_g0 :
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT0).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT1).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT2).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT3).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT4).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT5).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT6).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT7).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT8).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT9).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT10).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT11).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT12).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT13).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT14).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT15).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT16).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT17).pairs = 1020 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 18..35. -/
theorem s6c6p_hp_g1 :
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT18).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT19).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT20).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT21).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT22).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT23).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT24).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT25).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT26).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT27).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT28).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT29).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT30).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT31).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT32).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT33).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT34).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT35).pairs = (4 : ℚ)
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 18..35. -/
theorem s6c6p_sp_g1 :
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT18).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT19).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT20).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT21).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT22).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT23).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT24).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT25).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT26).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT27).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT28).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT29).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT30).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT31).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT32).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT33).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT34).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT35).pairs = 128 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 36..53. -/
theorem s6c6p_hp_g2 :
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT36).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT37).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT38).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT39).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT40).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT41).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT42).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT43).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT44).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT45).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT46).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT47).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT48).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT49).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT50).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT51).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT52).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT53).pairs = (25 : ℚ)
        / 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 36..53. -/
theorem s6c6p_sp_g2 :
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT36).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT37).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT38).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT39).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT40).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT41).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT42).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT43).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT44).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT45).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT46).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT47).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT48).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT49).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT50).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT51).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT52).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT53).pairs = 400 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 54..59. -/
theorem s6c6p_hp_g3 :
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT54).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT55).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT56).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT57).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT58).pairs +
    pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT59).pairs = (5 : ℚ)
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 54..59. -/
theorem s6c6p_sp_g3 :
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT54).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT55).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT56).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT57).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT58).pairs +
    selfPairsB s6c6pW (ShortData.ofList s6c6pGT59).pairs = 160 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The diagonal terms of the matrix part with the pair contributions equal the matrix self part. -/
theorem s6c6p_hm_rest : triMatDiag (sixthSrcMatZ.act s6c6pH) (sixthSrcMatZ.act s6c6pG) +
    s6c6pL.sden * ((54656 : ℤ) : ℚ) / ((sixthSrcMatZ.act s6c6pG).den * 4 ^ (sixthSrcMatZ.act
        s6c6pG).k) = selfMatZI (sixthSrcMatZ.act s6c6pG) := by
  decide +kernel

/-- The matrix part equals the matrix self part of the target. -/
theorem s6c6p_hm : triMatF true s6c6pL s6c6pW = selfMatQ s6c6pW := by
  rw [triMatF_eq_ZI true s6c6pL s6c6pW (sixthSrcMatZ.act s6c6pH) (sixthSrcMatZ.act s6c6pG)
      (sixthSrcMat_act_entryZ s6c6pH) (sixthSrcMat_act_entryZ s6c6pG),
    selfMatQ_eq_ZI s6c6pW (sixthSrcMatZ.act s6c6pG) (sixthSrcMat_act_entryZ s6c6pG), triMatZI_eq_B]
  have hp : triMatPB true (sixthSrcMatZ.act s6c6pG) s6c6pL.sh.pairs = 54656 := by
    show triMatPB true (sixthSrcMatZ.act s6c6pG) (ShortData.ofList s6c6pHT).pairs = _
    simp only [s6c6pHT, ofList_pairs_append, triMatPB_append]
    linarith [s6c6p_hm_g0, s6c6p_hm_g1, s6c6p_hm_g2, s6c6p_hm_g3]
  rw [hp]
  exact s6c6p_hm_rest

/-- The pair part equals the pair self part of the target. -/
theorem s6c6p_hp : pairSumQ true s6c6pL s6c6pW = s6c6pW.sden * (selfPairsZ s6c6pW : ℚ) := by
  rw [pairSumQ_eq_ZI true s6c6pL s6c6pW (sixthSrcMatZ.act s6c6pH) (sixthSrcMat_act_entryZ s6c6pH),
      pairSumZI_eq_B, selfPairsZ_eq_B]
  have h1 : pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL s6c6pW.sh.pairs = (427 : ℚ) / 8 := by
    show pairSumQB true (sixthSrcMatZ.act s6c6pH) s6c6pL (ShortData.ofList s6c6pGT).pairs = _
    simp only [s6c6pGT, ofList_pairs_append, pairSumQB_append]
    linarith [s6c6p_hp_g0, s6c6p_hp_g1, s6c6p_hp_g2, s6c6p_hp_g3]
  have h2 : selfPairsB s6c6pW s6c6pW.sh.pairs = 1708 := by
    show selfPairsB s6c6pW (ShortData.ofList s6c6pGT).pairs = _
    simp only [s6c6pGT, ofList_pairs_append, selfPairsB_append]
    linarith [s6c6p_sp_g0, s6c6p_sp_g1, s6c6p_sp_g2, s6c6p_sp_g3]
  rw [h1, h2]
  show (427 : ℚ) / 8 = 1 / 32 * ((1708 : ℤ) : ℚ)
  norm_num

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
