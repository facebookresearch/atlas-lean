/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC20nLW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib2

/-! # Parts (octad check, matrix, pairs) of the identification Seventh cell record S7c20-
(gforest:S7c20-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem s7c20n_hok : octPackOk 40 s7c20nL = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 0..17. -/
theorem s7c20n_hm_g0 :
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT0).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT1).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT2).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT3).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT4).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT5).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT6).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT7).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT8).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT9).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT10).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT11).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT12).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT13).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT14).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT15).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT16).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT17).pairs = 1179648 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 18..35. -/
theorem s7c20n_hm_g1 :
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT18).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT19).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT20).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT21).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT22).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT23).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT24).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT25).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT26).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT27).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT28).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT29).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT30).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT31).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT32).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT33).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT34).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT35).pairs = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair contributions to the matrix part over the source chunks 36..53. -/
theorem s7c20n_hm_g2 :
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT36).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT37).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT38).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT39).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT40).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT41).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT42).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT43).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT44).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT45).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT46).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT47).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT48).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT49).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT50).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT51).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT52).pairs +
    triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT53).pairs = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 0..17. -/
theorem s7c20n_hp_g0 :
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT0).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT1).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT2).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT3).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT4).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT5).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT6).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT7).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT8).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT9).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT10).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT11).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT12).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT13).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT14).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT15).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT16).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT17).pairs =
        (7872 : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 0..17. -/
theorem s7c20n_sp_g0 :
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT0).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT1).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT2).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT3).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT4).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT5).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT6).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT7).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT8).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT9).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT10).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT11).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT12).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT13).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT14).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT15).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT16).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT17).pairs = 64487424 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 18..35. -/
theorem s7c20n_hp_g1 :
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT18).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT19).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT20).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT21).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT22).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT23).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT24).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT25).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT26).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT27).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT28).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT29).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT30).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT31).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT32).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT33).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT34).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT35).pairs =
        (1792 : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 18..35. -/
theorem s7c20n_sp_g1 :
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT18).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT19).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT20).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT21).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT22).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT23).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT24).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT25).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT26).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT27).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT28).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT29).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT30).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT31).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT32).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT33).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT34).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT35).pairs = 14680064 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part over the target chunks 36..53. -/
theorem s7c20n_hp_g2 :
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT36).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT37).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT38).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT39).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT40).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT41).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT42).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT43).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT44).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT45).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT46).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT47).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT48).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT49).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT50).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT51).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT52).pairs +
    pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT53).pairs = (0
        : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair self part of the target over the target chunks 36..53. -/
theorem s7c20n_sp_g2 :
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT36).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT37).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT38).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT39).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT40).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT41).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT42).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT43).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT44).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT45).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT46).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT47).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT48).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT49).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT50).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT51).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT52).pairs +
    selfPairsB s7c20nW (ShortData.ofList s7c20nGT53).pairs = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The diagonal terms of the matrix part with the pair contributions equal the matrix self part. -/
theorem s7c20n_hm_rest : triMatDiag (srcSeventhMatZ.act s7c20nH) (srcSeventhMatZ.act s7c20nG) +
    s7c20nL.sden * ((1179648 : ℤ) : ℚ) / ((srcSeventhMatZ.act s7c20nG).den * 4 ^
        (srcSeventhMatZ.act s7c20nG).k) = selfMatZI (srcSeventhMatZ.act s7c20nG) := by
  decide +kernel

/-- The matrix part equals the matrix self part of the target. -/
theorem s7c20n_hm : triMatF false s7c20nL s7c20nW = selfMatQ s7c20nW := by
  rw [triMatF_eq_ZI false s7c20nL s7c20nW (srcSeventhMatZ.act s7c20nH) (srcSeventhMatZ.act
      s7c20nG) (srcSeventhMat_act_entryZ s7c20nH) (srcSeventhMat_act_entryZ s7c20nG),
    selfMatQ_eq_ZI s7c20nW (srcSeventhMatZ.act s7c20nG) (srcSeventhMat_act_entryZ s7c20nG),
        triMatZI_eq_B]
  have hp : triMatPB false (srcSeventhMatZ.act s7c20nG) s7c20nL.sh.pairs = 1179648 := by
    show triMatPB false (srcSeventhMatZ.act s7c20nG) (ShortData.ofList s7c20nHT).pairs = _
    simp only [s7c20nHT, ofList_pairs_append, triMatPB_append]
    linarith [s7c20n_hm_g0, s7c20n_hm_g1, s7c20n_hm_g2]
  rw [hp]
  exact s7c20n_hm_rest

/-- The pair part equals the pair self part of the target. -/
theorem s7c20n_hp : pairSumQ false s7c20nL s7c20nW = s7c20nW.sden * (selfPairsZ s7c20nW : ℚ) := by
  rw [pairSumQ_eq_ZI false s7c20nL s7c20nW (srcSeventhMatZ.act s7c20nH) (srcSeventhMat_act_entryZ
      s7c20nH), pairSumZI_eq_B, selfPairsZ_eq_B]
  have h1 : pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL s7c20nW.sh.pairs = (9664 : ℚ) := by
    show pairSumQB false (srcSeventhMatZ.act s7c20nH) s7c20nL (ShortData.ofList s7c20nGT).pairs = _
    simp only [s7c20nGT, ofList_pairs_append, pairSumQB_append]
    linarith [s7c20n_hp_g0, s7c20n_hp_g1, s7c20n_hp_g2]
  have h2 : selfPairsB s7c20nW s7c20nW.sh.pairs = 79167488 := by
    show selfPairsB s7c20nW (ShortData.ofList s7c20nGT).pairs = _
    simp only [s7c20nGT, ofList_pairs_append, selfPairsB_append]
    linarith [s7c20n_sp_g0, s7c20n_sp_g1, s7c20n_sp_g2]
  rw [h1, h2]
  show (9664 : ℚ) = 1 / srcSeventhD0 * ((79167488 : ℤ) : ℚ)
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
