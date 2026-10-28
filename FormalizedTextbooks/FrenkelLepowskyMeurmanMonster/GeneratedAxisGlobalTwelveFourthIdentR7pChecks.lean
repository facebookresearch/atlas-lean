/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR7pWShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSX7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctGM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Data checks of the Fourth identification `R7p` (Seventh target)

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
def fourthR7pHP : List TPlan :=
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
      [(1, false), (0, false)]
      [.trans 10 11, .trans 0 10, .trans 1 6, .trans 4 1, .trans 1 0, .trans 10 4, .trans 4 3,
        .trans 1 2, .trans 9 10, .trans 6 0, .trans 0 5, .trans 4 6, .trans 6 1,
        .trans 7 1, .trans 2 1, .trans 1 4, .trans 10 11, .trans 0 7, .trans 3 6,
        .trans 1 8, .trans 8 3, .trans 8 9, .trans 9 2, .trans 2 9, .trans 9 2,
        .trans 0 11, .trans 3 8, .trans 4 5, .trans 5 0, .trans 5 9, .trans 5 11,
        .trans 6 0, .trans 6 7, .trans 6 11, .trans 7 3, .trans 7 8, .trans 8 3,
        .trans 8 4, .trans 8 5, .trans 8 6, .trans 8 7, .trans 8 9]]

/-- The tensor plan of the target word. -/
def fourthR7pGP : List TPlan :=
  [.letter (.qel (qmElt (14983992, false))),
    .letter (.sign 552 0),
    .run
      [(0, true), (0, true), (1, false), (0, true), (1, false), (0, true), (0, true),
        (0, true), (1, false), (0, true), (0, true), (0, true), (1, false), (0, false),
        (0, false), (1, false), (0, true), (1, false), (0, false), (0, false),
        (1, false), (0, true), (1, false), (0, false), (0, false), (1, true), (0, true),
        (0, true), (1, true), (0, true), (1, true), (0, true), (0, true), (1, true),
        (0, true), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false),
        (0, false), (1, true), (0, false), (1, true), (0, false), (0, false), (1, false),
        (0, true), (0, true), (1, false), (0, false), (1, false), (0, true), (0, true),
        (1, false), (0, false), (1, false), (0, false), (0, false), (1, false),
        (0, true), (0, true), (1, false), (0, true), (0, true), (1, false), (0, false)]
      [.trans 0 1, .trans 0 2, .trans 0 3, .trans 0 6, .trans 0 8, .trans 2 1, .trans 1 2,
        .trans 1 3, .trans 1 4, .trans 1 6, .trans 1 8, .trans 4 2, .trans 2 0,
        .trans 2 4, .trans 6 3, .trans 3 0, .trans 3 6, .trans 3 8, .trans 5 4,
        .trans 4 0, .trans 4 3, .trans 4 5, .trans 4 8, .trans 5 0, .trans 5 1,
        .trans 5 2, .trans 5 4, .trans 5 6, .trans 5 7, .trans 5 9, .trans 5 10,
        .trans 6 1, .trans 6 7, .trans 6 9, .trans 6 10, .trans 8 7, .trans 7 0,
        .trans 7 1, .trans 7 2, .trans 7 4, .trans 7 5, .trans 7 6, .trans 7 8,
        .trans 8 0, .trans 8 3, .trans 8 4, .trans 8 9, .trans 10 9, .trans 9 1,
        .trans 9 3, .trans 9 6, .trans 9 7, .trans 9 10, .trans 10 0, .trans 10 1,
        .trans 10 3, .trans 10 5, .trans 10 8],
    .letter (.xi),
    .letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6],
    .letter (.xi),
    .letter (.xi)]

/-- The packed tensor of the image of the Fourth axis. -/
def fourthR7pHX : List SVec := tensorPlanF 104 fourthR7pHP (fourthSrcXW 104)

/-- The packed tensor of the Seventh source vector (kernel-feasible copy). -/
def fourthR7pSX : List SVec :=
  seventhSXF 104

/-- The tensor denominator of the Seventh source vector. -/
def fourthR7pSD : ℚ := (2 * ((tensorWordDenAll srcSeventhH : ℚ) * 1))

/-- The packed tensor of the image of the Seventh representative. -/
def fourthR7pGX : List SVec := tensorPlanF 104 fourthR7pGP fourthR7pSX

/-- The representation of the image of the Fourth axis. -/
def fourthR7pL : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthR7pH, ShortData.ofList fourthR7pHT, 1 / 8,
    tensorRat 104 fourthR7pHX ((tensorWordDenAll fourthR7pH : ℚ) * 1)⟩

/-- The representation of the image of the Seventh representative. -/
def fourthR7pW : IdentVec :=
  ⟨(seventhSrcVecW 104).mat.act identSpatialAlphabet fourthR7pG, ShortData.ofList fourthR7pGT,
    (seventhSrcVecW 104).sden,
    tensorRat 104 fourthR7pGX ((tensorWordDenAll fourthR7pG : ℚ) * fourthR7pSD)⟩

set_option maxRecDepth 100000 in
/-- The plan of the source word expands to the source word. -/
theorem fourthR7pHP_word : planWord fourthR7pHP = fourthR7pH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word expands to the target word. -/
theorem fourthR7pGP_word : planWord fourthR7pGP = fourthR7pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of both plans are admissible. -/
theorem fourthR7pP_ok : planOk fourthR7pHP = true ∧ planOk fourthR7pGP = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem fourthR7pH_check :
    (fourthWordData fourthR7pH).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem fourthR7pG_check :
    (fourthWordData fourthR7pG).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fourthR7pD_ok : fourthR7pHD.ok = true ∧ fourthR7pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem fourthR7pHD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthR7pH).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthR7pHD.colsP i.val, fourthR7pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem fourthR7pGD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthR7pG).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthR7pGD.colsP i.val, fourthR7pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem fourthR7pHD_rows : ∀ i : Fin 24,
    fld 24 fourthR7pHD.rowsP i.val = rowsOf (fun j => fld 24 fourthR7pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem fourthR7pGD_rows : ∀ i : Fin 24,
    fld 24 fourthR7pGD.rowsP i.val = rowsOf (fun j => fld 24 fourthR7pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the Fourth image is transported onto the literal targets. -/
theorem fourthR7pHT_check : shortCheckF fourthR7pHD fourthSrcShort.flat fourthR7pHT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The target short list is the transport of the literal Seventh source short list. -/
theorem fourthR7p_wcheck :
    shortCheckF fourthR7pGD fourthSrcLit7Chunks.flatten fourthR7pGT = true := by
  have hl : fourthSrcLit7Chunks.length = fourthR7pGTChunks.length := by
    rw [fourthSrcLit7Chunks_length]
    rfl
  apply shortCheckF_flatten fourthR7pGD _ _ hl fourthR7p_wlens
  intro i hi
  rw [fourthSrcLit7Chunks_length] at hi
  interval_cases i
  · exact fourthR7p_wchunk0
  · exact fourthR7p_wchunk1
  · exact fourthR7p_wchunk2
  · exact fourthR7p_wchunk3
  · exact fourthR7p_wchunk4
  · exact fourthR7p_wchunk5
  · exact fourthR7p_wchunk6
  · exact fourthR7p_wchunk7
  · exact fourthR7p_wchunk8
  · exact fourthR7p_wchunk9
  · exact fourthR7p_wchunk10
  · exact fourthR7p_wchunk11
  · exact fourthR7p_wchunk12
  · exact fourthR7p_wchunk13
  · exact fourthR7p_wchunk14
  · exact fourthR7p_wchunk15
  · exact fourthR7p_wchunk16
  · exact fourthR7p_wchunk17
  · exact fourthR7p_wchunk18
  · exact fourthR7p_wchunk19
  · exact fourthR7p_wchunk20
  · exact fourthR7p_wchunk21
  · exact fourthR7p_wchunk22
  · exact fourthR7p_wchunk23
  · exact fourthR7p_wchunk24
  · exact fourthR7p_wchunk25
  · exact fourthR7p_wchunk26
  · exact fourthR7p_wchunk27
  · exact fourthR7p_wchunk28

/-- The short block of the Seventh image is transported onto the literal targets. -/
theorem fourthR7pGT_check :
    shortCheckF fourthR7pGD (seventhSrcVecW 104).sh.flat fourthR7pGT = true := by
  rw [fourthSrcLit7_eq]
  exact fourthR7p_wcheck

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem fourthR7pT_labels : fourthR7pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    fourthR7pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem fourthR7pH_growth : tensorWordGrowthAll fourthR7pH * 56 = 3670016 := by decide

/-- The word bound of the target word. -/
theorem fourthR7pG_growth :
    tensorWordGrowthAll fourthR7pG * (4 * (16777216 * 8) + 276 * 6144) =
      18505009393888657408 := by
  decide

/-- The tensor bound of the image of the Fourth axis. -/
theorem fourthR7pHX_bnd : TBnd 104 3670016 fourthR7pHX := by
  have h := (tensorPlanF_actual fourthR7pHP fourthR7pP_ok.1 (fourthSrcXW_bnd (w := 104) (by norm_num))
    (by rw [fourthR7pHP_word, fourthR7pH_growth]; norm_num) 1).1
  rw [fourthR7pHP_word, fourthR7pH_growth] at h
  exact h

/-- The tensor bound of the image of the Seventh representative. -/
theorem fourthR7pGX_bnd : TBnd 104 18505009393888657408 fourthR7pGX := by
  have h := (tensorPlanF_actual fourthR7pGP fourthR7pP_ok.2 (seventhSXF_bndB (w := 104) (by norm_num))
    (by rw [fourthR7pGP_word, fourthR7pG_growth]; norm_num) fourthR7pSD).1
  rw [fourthR7pGP_word, fourthR7pG_growth] at h
  exact h

/-- The coordinates of the Fourth image. -/
theorem fourthR7pL_actual : griessConwayEncode (rhoLocal (identWordLocal fourthR7pH)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthR7pL.real := by
  have hT := (tensorPlanF_actual fourthR7pHP fourthR7pP_ok.1 (fourthSrcXW_bnd (w := 104) (by norm_num))
    (by rw [fourthR7pHP_word, fourthR7pH_growth]; norm_num) 1).2
  rw [fourthR7pHP_word] at hT
  rw [← fourthWordData_fst fourthR7pH] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 104) (fourthWordData fourthR7pH) fourthR7pH_check
    fourthR7pHD fourthR7pD_ok.1 fourthR7pHD_cols fourthR7pHD_rows fourthR7pHT
    fourthR7pHT_check _ hT _ (fourthSrcW_rep (by norm_num))

/-- The coordinates of the Seventh image. -/
theorem fourthR7pW_actual : griessConwayEncode (rhoLocal (identWordLocal fourthR7pG)
    (generatedAxisGlobalTwelveRepresentative 6)) = fourthR7pW.real := by
  have hT := (tensorPlanF_actual fourthR7pGP fourthR7pP_ok.2 (seventhSXF_bndB (w := 104) (by norm_num))
    (by rw [fourthR7pGP_word, fourthR7pG_growth]; norm_num) fourthR7pSD).2
  rw [fourthR7pGP_word] at hT
  rw [show tensorRat 104 (seventhSXF 104) fourthR7pSD = (seventhSrcVecW 104).ten from
    seventhSXF104_ten] at hT
  rw [← fourthWordData_fst fourthR7pG] at hT ⊢
  exact IdentVec.word_actual (seventhSrcVecW 104) (fourthWordData fourthR7pG) fourthR7pG_check
    fourthR7pGD fourthR7pD_ok.2 fourthR7pGD_cols fourthR7pGD_rows fourthR7pGT
    fourthR7pGT_check _ hT _ (seventhSrcW_rep (by norm_num))

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
