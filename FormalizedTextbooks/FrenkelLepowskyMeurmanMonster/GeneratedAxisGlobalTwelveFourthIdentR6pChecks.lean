/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR6pWShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSX7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctGM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Data checks of the Fourth identification `R6p` (Seventh target)

The source side is the image of the Fourth axis under the translated root word
(`fourthSrcVecW 104`), the target side the image of the Seventh representative under the target
word (`seventhSrcVecW 104`, worker `gforest`); both representations are computed by the word
actions and bound to the genuine coordinates here.  The packed tensors are evaluated by tensor
plans with fused monomial runs (`tensorPlanF`, gtenth); the Seventh source tensor enters through
the kernel-feasible copy `seventhSXF 104` with the same rational tensor.  The target short transport is
checked chunkwise. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor plan of the source word. -/
def fourthR6pHP : List TPlan :=
  [.letter (.xi),
    .run
      [(0, false)]
      [.trans 0 11, .trans 0 10, .trans 8 3, .trans 9 11, .trans 7 6, .trans 7 0, .trans 0 1,
        .trans 5 0, .trans 8 2, .trans 9 2, .trans 10 6, .trans 10 4, .trans 0 8,
        .trans 6 7, .trans 4 5, .trans 7 3, .trans 10 1, .trans 4 3, .trans 5 2,
        .trans 6 2, .trans 2 9, .trans 9 8, .trans 1 8, .trans 8 3, .trans 3 9,
        .trans 9 11, .trans 9 2, .trans 8 11],
    .letter (.xi),
    .run
      [(1, false), (0, false), (1, false)]
      [.trans 3 0, .trans 0 3, .trans 0 4, .trans 0 8, .trans 0 9, .trans 0 10, .trans 0 11,
        .trans 1 2, .trans 1 3, .trans 3 2, .trans 2 0, .trans 2 3, .trans 2 4,
        .trans 3 1, .trans 3 4, .trans 3 5, .trans 3 8, .trans 3 9, .trans 3 10,
        .trans 3 11, .trans 4 0, .trans 4 9, .trans 4 10, .trans 5 4, .trans 5 8,
        .trans 5 9, .trans 8 6, .trans 6 1, .trans 6 2, .trans 6 3, .trans 6 5,
        .trans 6 8, .trans 6 9, .trans 9 7, .trans 7 0, .trans 7 1, .trans 7 2,
        .trans 7 3, .trans 7 4, .trans 7 5, .trans 7 9, .trans 7 10, .trans 9 8,
        .trans 8 4, .trans 8 5, .trans 8 6, .trans 8 7, .trans 8 9, .trans 8 10,
        .trans 8 11, .trans 9 8, .trans 10 1, .trans 10 2, .trans 10 3, .trans 10 4,
        .trans 10 5, .trans 10 6, .trans 10 7, .trans 10 8, .trans 10 9]]

/-- The tensor plan of the target word. -/
def fourthR6pGP : List TPlan :=
  [.letter (.qel (qmElt (13431792, false))),
    .letter (.sign 1981 0),
    .run
      [(0, false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, false),
        (0, false), (0, false), (0, false), (1, false), (0, false), (0, false),
        (0, false), (1, false), (0, true), (1, false), (0, true), (1, false), (0, false),
        (0, false), (1, false), (0, false), (0, false), (0, false), (1, true),
        (0, false), (0, false), (1, true), (0, true), (1, true), (0, true), (0, true),
        (1, true), (0, false), (1, true), (0, true), (0, true), (0, true), (1, true),
        (0, true), (1, true), (0, false), (1, false), (0, false), (0, false), (1, false),
        (0, false), (1, false), (0, false), (0, false), (1, false), (0, true),
        (1, false), (0, true), (0, true), (1, false), (0, true), (0, true), (1, false),
        (0, true), (1, false), (0, true), (0, true), (1, false)]
      [.trans 0 7, .trans 2 11, .trans 10 4, .trans 1 5, .trans 8 3, .trans 7 3, .trans 5 4,
        .trans 4 0, .trans 3 2, .trans 3 4, .trans 5 6, .trans 8 7, .trans 0 7,
        .trans 1 7, .trans 9 10, .trans 4 1, .trans 8 6, .trans 9 1, .trans 1 0,
        .trans 7 8, .trans 7 10, .trans 10 4, .trans 9 6, .trans 6 8, .trans 10 3,
        .trans 6 2, .trans 5 8, .trans 0 6, .trans 1 4, .trans 1 11, .trans 2 0,
        .trans 2 6, .trans 4 9, .trans 6 3, .trans 6 5, .trans 8 0, .trans 8 1,
        .trans 8 2, .trans 8 4, .trans 8 9, .trans 8 11, .trans 9 0, .trans 9 1,
        .trans 9 2, .trans 9 4, .trans 9 5, .trans 9 8, .trans 9 11],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, false), (0, false)]
      [.trans 9 2, .trans 0 11, .trans 0 4, .trans 4 9, .trans 4 6, .trans 7 8, .trans 8 3,
        .trans 3 11, .trans 10 4, .trans 4 1, .trans 6 7, .trans 0 2, .trans 7 6,
        .trans 7 1, .trans 0 7, .trans 7 0, .trans 1 11, .trans 1 8, .trans 8 2,
        .trans 3 2, .trans 2 8, .trans 4 7, .trans 4 8, .trans 5 10, .trans 6 10,
        .trans 7 9, .trans 8 3, .trans 8 9, .trans 9 11, .trans 10 3, .trans 10 4,
        .trans 10 5, .trans 10 6, .trans 10 7, .trans 10 8]]

/-- The packed tensor of the image of the Fourth axis. -/
def fourthR6pHX : List SVec := tensorPlanF 104 fourthR6pHP (fourthSrcXW 104)

/-- The packed tensor of the Seventh source vector (kernel-feasible copy). -/
def fourthR6pSX : List SVec :=
  seventhSXF 104

/-- The tensor denominator of the Seventh source vector. -/
def fourthR6pSD : ℚ := (2 * ((tensorWordDenAll srcSeventhH : ℚ) * 1))

/-- The packed tensor of the image of the Seventh representative. -/
def fourthR6pGX : List SVec := tensorPlanF 104 fourthR6pGP fourthR6pSX

/-- The representation of the image of the Fourth axis. -/
def fourthR6pL : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthR6pH, ShortData.ofList fourthR6pHT, 1 / 8,
    tensorRat 104 fourthR6pHX ((tensorWordDenAll fourthR6pH : ℚ) * 1)⟩

/-- The representation of the image of the Seventh representative. -/
def fourthR6pW : IdentVec :=
  ⟨(seventhSrcVecW 104).mat.act identSpatialAlphabet fourthR6pG, ShortData.ofList fourthR6pGT,
    (seventhSrcVecW 104).sden,
    tensorRat 104 fourthR6pGX ((tensorWordDenAll fourthR6pG : ℚ) * fourthR6pSD)⟩

set_option maxRecDepth 100000 in
/-- The plan of the source word expands to the source word. -/
theorem fourthR6pHP_word : planWord fourthR6pHP = fourthR6pH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word expands to the target word. -/
theorem fourthR6pGP_word : planWord fourthR6pGP = fourthR6pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of both plans are admissible. -/
theorem fourthR6pP_ok : planOk fourthR6pHP = true ∧ planOk fourthR6pGP = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem fourthR6pH_check :
    (fourthWordData fourthR6pH).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem fourthR6pG_check :
    (fourthWordData fourthR6pG).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fourthR6pD_ok : fourthR6pHD.ok = true ∧ fourthR6pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem fourthR6pHD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthR6pH).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthR6pHD.colsP i.val, fourthR6pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem fourthR6pGD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthR6pG).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthR6pGD.colsP i.val, fourthR6pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem fourthR6pHD_rows : ∀ i : Fin 24,
    fld 24 fourthR6pHD.rowsP i.val = rowsOf (fun j => fld 24 fourthR6pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem fourthR6pGD_rows : ∀ i : Fin 24,
    fld 24 fourthR6pGD.rowsP i.val = rowsOf (fun j => fld 24 fourthR6pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the Fourth image is transported onto the literal targets. -/
theorem fourthR6pHT_check : shortCheckF fourthR6pHD fourthSrcShort.flat fourthR6pHT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The target short list is the transport of the literal Seventh source short list. -/
theorem fourthR6p_wcheck :
    shortCheckF fourthR6pGD fourthSrcLit7Chunks.flatten fourthR6pGT = true := by
  have hl : fourthSrcLit7Chunks.length = fourthR6pGTChunks.length := by
    rw [fourthSrcLit7Chunks_length]
    rfl
  apply shortCheckF_flatten fourthR6pGD _ _ hl fourthR6p_wlens
  intro i hi
  rw [fourthSrcLit7Chunks_length] at hi
  interval_cases i
  · exact fourthR6p_wchunk0
  · exact fourthR6p_wchunk1
  · exact fourthR6p_wchunk2
  · exact fourthR6p_wchunk3
  · exact fourthR6p_wchunk4
  · exact fourthR6p_wchunk5
  · exact fourthR6p_wchunk6
  · exact fourthR6p_wchunk7
  · exact fourthR6p_wchunk8
  · exact fourthR6p_wchunk9
  · exact fourthR6p_wchunk10
  · exact fourthR6p_wchunk11
  · exact fourthR6p_wchunk12
  · exact fourthR6p_wchunk13
  · exact fourthR6p_wchunk14
  · exact fourthR6p_wchunk15
  · exact fourthR6p_wchunk16
  · exact fourthR6p_wchunk17
  · exact fourthR6p_wchunk18
  · exact fourthR6p_wchunk19
  · exact fourthR6p_wchunk20
  · exact fourthR6p_wchunk21
  · exact fourthR6p_wchunk22
  · exact fourthR6p_wchunk23
  · exact fourthR6p_wchunk24
  · exact fourthR6p_wchunk25
  · exact fourthR6p_wchunk26
  · exact fourthR6p_wchunk27
  · exact fourthR6p_wchunk28

/-- The short block of the Seventh image is transported onto the literal targets. -/
theorem fourthR6pGT_check :
    shortCheckF fourthR6pGD (seventhSrcVecW 104).sh.flat fourthR6pGT = true := by
  rw [fourthSrcLit7_eq]
  exact fourthR6p_wcheck

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem fourthR6pT_labels : fourthR6pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    fourthR6pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem fourthR6pH_growth : tensorWordGrowthAll fourthR6pH * 56 = 3670016 := by decide

/-- The word bound of the target word. -/
theorem fourthR6pG_growth :
    tensorWordGrowthAll fourthR6pG * (4 * (16777216 * 8) + 276 * 6144) =
      282364034940928 := by
  decide

/-- The tensor bound of the image of the Fourth axis. -/
theorem fourthR6pHX_bnd : TBnd 104 3670016 fourthR6pHX := by
  have h := (tensorPlanF_actual fourthR6pHP fourthR6pP_ok.1 (fourthSrcXW_bnd (w := 104) (by norm_num))
    (by rw [fourthR6pHP_word, fourthR6pH_growth]; norm_num) 1).1
  rw [fourthR6pHP_word, fourthR6pH_growth] at h
  exact h

/-- The tensor bound of the image of the Seventh representative. -/
theorem fourthR6pGX_bnd : TBnd 104 282364034940928 fourthR6pGX := by
  have h := (tensorPlanF_actual fourthR6pGP fourthR6pP_ok.2 (seventhSXF_bndB (w := 104) (by norm_num))
    (by rw [fourthR6pGP_word, fourthR6pG_growth]; norm_num) fourthR6pSD).1
  rw [fourthR6pGP_word, fourthR6pG_growth] at h
  exact h

/-- The coordinates of the Fourth image. -/
theorem fourthR6pL_actual : griessConwayEncode (rhoLocal (identWordLocal fourthR6pH)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthR6pL.real := by
  have hT := (tensorPlanF_actual fourthR6pHP fourthR6pP_ok.1 (fourthSrcXW_bnd (w := 104) (by norm_num))
    (by rw [fourthR6pHP_word, fourthR6pH_growth]; norm_num) 1).2
  rw [fourthR6pHP_word] at hT
  rw [← fourthWordData_fst fourthR6pH] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 104) (fourthWordData fourthR6pH) fourthR6pH_check
    fourthR6pHD fourthR6pD_ok.1 fourthR6pHD_cols fourthR6pHD_rows fourthR6pHT
    fourthR6pHT_check _ hT _ (fourthSrcW_rep (by norm_num))

/-- The coordinates of the Seventh image. -/
theorem fourthR6pW_actual : griessConwayEncode (rhoLocal (identWordLocal fourthR6pG)
    (generatedAxisGlobalTwelveRepresentative 6)) = fourthR6pW.real := by
  have hT := (tensorPlanF_actual fourthR6pGP fourthR6pP_ok.2 (seventhSXF_bndB (w := 104) (by norm_num))
    (by rw [fourthR6pGP_word, fourthR6pG_growth]; norm_num) fourthR6pSD).2
  rw [fourthR6pGP_word] at hT
  rw [show tensorRat 104 (seventhSXF 104) fourthR6pSD = (seventhSrcVecW 104).ten from
    seventhSXF104_ten] at hT
  rw [← fourthWordData_fst fourthR6pG] at hT ⊢
  exact IdentVec.word_actual (seventhSrcVecW 104) (fourthWordData fourthR6pG) fourthR6pG_check
    fourthR6pGD fourthR6pD_ok.2 fourthR6pGD_cols fourthR6pGD_rows fourthR6pGT
    fourthR6pGT_check _ hT _ (seventhSrcW_rep (by norm_num))

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
