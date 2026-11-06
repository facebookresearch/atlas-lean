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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfth

/-! # Parts (octad check, matrix, pairs) of the identification Seventh cell record S7c11+
(gforest:S7c11+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem s7c11p_hok : octPackOk 40 s7c11pL = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 0..17. -/
theorem s7c11p_hm_g0 :
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT0).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT1).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT2).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT3).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT4).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT5).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT6).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT7).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT8).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT9).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT10).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT11).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT12).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT13).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT14).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT15).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT16).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT17).pairs = 262144 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 18..35. -/
theorem s7c11p_hm_g1 :
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT18).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT19).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT20).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT21).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT22).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT23).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT24).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT25).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT26).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT27).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT28).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT29).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT30).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT31).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT32).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT33).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT34).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT35).pairs = 65536 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 36..53. -/
theorem s7c11p_hm_g2 :
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT36).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT37).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT38).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT39).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT40).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT41).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT42).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT43).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT44).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT45).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT46).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT47).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT48).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT49).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT50).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT51).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT52).pairs +
    triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT53).pairs = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 0..17. -/
theorem s7c11p_hp_g0 :
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT0).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT1).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT2).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT3).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT4).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT5).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT6).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT7).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT8).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT9).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT10).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT11).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT12).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT13).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT14).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT15).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT16).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT17).pairs = (24
        : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 0..17. -/
theorem s7c11p_sp_g0 :
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT0).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT1).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT2).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT3).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT4).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT5).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT6).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT7).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT8).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT9).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT10).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT11).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT12).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT13).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT14).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT15).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT16).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT17).pairs = 3072 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 18..35. -/
theorem s7c11p_hp_g1 :
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT18).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT19).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT20).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT21).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT22).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT23).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT24).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT25).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT26).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT27).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT28).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT29).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT30).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT31).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT32).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT33).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT34).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT35).pairs = (28
        : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 18..35. -/
theorem s7c11p_sp_g1 :
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT18).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT19).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT20).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT21).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT22).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT23).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT24).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT25).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT26).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT27).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT28).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT29).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT30).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT31).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT32).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT33).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT34).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT35).pairs = 3584 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 36..53. -/
theorem s7c11p_hp_g2 :
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT36).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT37).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT38).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT39).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT40).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT41).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT42).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT43).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT44).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT45).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT46).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT47).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT48).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT49).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT50).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT51).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT52).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT53).pairs = (10
        : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 36..53. -/
theorem s7c11p_sp_g2 :
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT36).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT37).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT38).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT39).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT40).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT41).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT42).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT43).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT44).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT45).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT46).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT47).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT48).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT49).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT50).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT51).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT52).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT53).pairs = 1280 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 54..71. -/
theorem s7c11p_hp_g3 :
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT54).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT55).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT56).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT57).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT58).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT59).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT60).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT61).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT62).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT63).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT64).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT65).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT66).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT67).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT68).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT69).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT70).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT71).pairs = (0 :
        ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 54..71. -/
theorem s7c11p_sp_g3 :
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT54).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT55).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT56).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT57).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT58).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT59).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT60).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT61).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT62).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT63).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT64).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT65).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT66).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT67).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT68).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT69).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT70).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT71).pairs = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 72..89. -/
theorem s7c11p_hp_g4 :
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT72).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT73).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT74).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT75).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT76).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT77).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT78).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT79).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT80).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT81).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT82).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT83).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT84).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT85).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT86).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT87).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT88).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT89).pairs = (0 :
        ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 72..89. -/
theorem s7c11p_sp_g4 :
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT72).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT73).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT74).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT75).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT76).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT77).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT78).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT79).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT80).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT81).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT82).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT83).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT84).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT85).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT86).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT87).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT88).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT89).pairs = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 90..91. -/
theorem s7c11p_hp_g5 :
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT90).pairs +
    pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT91).pairs = (0 :
        ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 90..91. -/
theorem s7c11p_sp_g5 :
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT90).pairs +
    selfPairsB s7c11pW (ShortData.ofList s7c11pGT91).pairs = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The diagonal terms of the matrix part with the pair contributions equal the matrix self part. -/
theorem s7c11p_hm_rest : triMatDiag (srcSeventhMatZ.act s7c11pH) (twelfthSrcMatZ.act s7c11pG) +
    s7c11pL.sden * ((327680 : ℤ) : ℚ) / ((twelfthSrcMatZ.act s7c11pG).den * 4 ^
        (twelfthSrcMatZ.act s7c11pG).k) = selfMatZI (twelfthSrcMatZ.act s7c11pG) := by
  decide +kernel

/-- The matrix part equals the matrix self part of the target. -/
theorem s7c11p_hm : triMatF true s7c11pL s7c11pW = selfMatQ s7c11pW := by
  rw [triMatF_eq_ZI true s7c11pL s7c11pW (srcSeventhMatZ.act s7c11pH) (twelfthSrcMatZ.act s7c11pG)
      (srcSeventhMat_act_entryZ s7c11pH) (twelfthSrcMat_act_entryZ s7c11pG),
    selfMatQ_eq_ZI s7c11pW (twelfthSrcMatZ.act s7c11pG) (twelfthSrcMat_act_entryZ s7c11pG),
        triMatZI_eq_B]
  have hp : triMatPB true (twelfthSrcMatZ.act s7c11pG) s7c11pL.sh.pairs = 327680 := by
    show triMatPB true (twelfthSrcMatZ.act s7c11pG) (ShortData.ofList s7c11pHT).pairs = _
    simp only [s7c11pHT, ofList_pairs_append, triMatPB_append]
    linarith [s7c11p_hm_g0, s7c11p_hm_g1, s7c11p_hm_g2]
  rw [hp]
  exact s7c11p_hm_rest

/-- The pair part equals the pair self part of the target. -/
theorem s7c11p_hp : pairSumQ true s7c11pL s7c11pW = s7c11pW.sden * (selfPairsZ s7c11pW : ℚ) := by
  rw [pairSumQ_eq_ZI true s7c11pL s7c11pW (srcSeventhMatZ.act s7c11pH) (srcSeventhMat_act_entryZ
      s7c11pH), pairSumZI_eq_B, selfPairsZ_eq_B]
  have h1 : pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL s7c11pW.sh.pairs = (62 : ℚ) := by
    show pairSumQB true (srcSeventhMatZ.act s7c11pH) s7c11pL (ShortData.ofList s7c11pGT).pairs = _
    simp only [s7c11pGT, ofList_pairs_append, pairSumQB_append]
    linarith [s7c11p_hp_g0, s7c11p_hp_g1, s7c11p_hp_g2, s7c11p_hp_g3, s7c11p_hp_g4, s7c11p_hp_g5]
  have h2 : selfPairsB s7c11pW s7c11pW.sh.pairs = 7936 := by
    show selfPairsB s7c11pW (ShortData.ofList s7c11pGT).pairs = _
    simp only [s7c11pGT, ofList_pairs_append, selfPairsB_append]
    linarith [s7c11p_sp_g0, s7c11p_sp_g1, s7c11p_sp_g2, s7c11p_sp_g3, s7c11p_sp_g4, s7c11p_sp_g5]
  rw [h1, h2]
  show (62 : ℚ) = 1 / 128 * ((7936 : ℤ) : ℚ)
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
