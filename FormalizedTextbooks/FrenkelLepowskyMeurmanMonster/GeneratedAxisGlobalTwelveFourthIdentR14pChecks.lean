/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14pWShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSX7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctGM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Data checks of the Fourth identification `R14p` (Seventh target)

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
def fourthR14pHP : List TPlan :=
  [.letter (.xi),
    .run
      [(1, false)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6],
    .letter (.xi),
    .run
      [(0, false), (1, false)]
      [.trans 3 11, .trans 7 6, .trans 4 5, .trans 11 2, .trans 10 3, .trans 4 1, .trans 1 8,
        .trans 9 7, .trans 6 10, .trans 10 9, .trans 3 7, .trans 6 2, .trans 10 11,
        .trans 7 4, .trans 11 4, .trans 10 8, .trans 5 1, .trans 1 9, .trans 4 2,
        .trans 2 3, .trans 9 11, .trans 8 0, .trans 2 0, .trans 5 6, .trans 7 9,
        .trans 9 8, .trans 8 3, .trans 8 11, .trans 8 10, .trans 8 7, .trans 0 5,
        .trans 1 0, .trans 1 5, .trans 3 4, .trans 4 2, .trans 4 7, .trans 4 9,
        .trans 5 6, .trans 5 11, .trans 6 0, .trans 6 1, .trans 6 2, .trans 6 3,
        .trans 6 4, .trans 6 7, .trans 6 9, .trans 9 10, .trans 11 2, .trans 11 4,
        .trans 11 7, .trans 11 9, .trans 11 10]]

/-- The tensor plan of the target word. -/
def fourthR14pGP : List TPlan :=
  [.letter (.qel (qmElt (11923762, false))),
    .letter (.sign 1276 0),
    .run
      [(0, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
        (0, true), (1, false), (0, false), (0, false), (0, false), (1, false),
        (0, false), (1, false), (0, false), (0, false), (1, false), (0, false),
        (1, false), (0, true), (0, true), (0, true), (1, true), (0, false), (1, true),
        (0, false), (1, true), (0, false), (0, false), (1, true), (0, false), (0, false),
        (1, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false),
        (0, false), (1, true), (0, true), (1, true), (0, false), (0, false), (0, false),
        (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
        (0, true), (1, false), (0, false), (1, false), (0, false), (1, false), (0, true),
        (0, true), (0, true), (1, false), (0, true), (0, true), (1, false), (0, true),
        (0, true), (0, true), (1, false)]
      [.trans 3 1, .trans 1 2, .trans 8 9, .trans 2 0, .trans 0 11, .trans 9 1, .trans 7 1,
        .trans 1 0, .trans 4 9, .trans 7 8, .trans 9 3, .trans 0 3, .trans 8 3,
        .trans 4 2, .trans 2 3, .trans 6 3, .trans 10 11, .trans 4 6, .trans 3 1,
        .trans 10 5, .trans 5 8, .trans 5 7, .trans 8 4, .trans 4 8, .trans 4 9,
        .trans 9 5, .trans 5 9, .trans 6 4, .trans 6 5, .trans 6 8, .trans 7 5,
        .trans 7 9, .trans 8 6, .trans 9 7],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, true), (0, true)]
      [.trans 1 2, .trans 8 3, .trans 10 5, .trans 8 9, .trans 2 8, .trans 4 7, .trans 7 0,
        .trans 4 8, .trans 8 3, .trans 5 9, .trans 5 4, .trans 10 6, .trans 6 4,
        .trans 6 8, .trans 5 10, .trans 10 1, .trans 0 4, .trans 3 2, .trans 2 11,
        .trans 7 6, .trans 6 7, .trans 6 9, .trans 0 2, .trans 9 11, .trans 4 6,
        .trans 7 10, .trans 10 11, .trans 9 2, .trans 6 1, .trans 1 11]]

/-- The packed tensor of the image of the Fourth axis. -/
def fourthR14pHX : List SVec := tensorPlanF 104 fourthR14pHP (fourthSrcXW 104)

/-- The packed tensor of the Seventh source vector (kernel-feasible copy). -/
def fourthR14pSX : List SVec :=
  seventhSXF 104

/-- The tensor denominator of the Seventh source vector. -/
def fourthR14pSD : ℚ := (2 * ((tensorWordDenAll srcSeventhH : ℚ) * 1))

/-- The packed tensor of the image of the Seventh representative. -/
def fourthR14pGX : List SVec := tensorPlanF 104 fourthR14pGP fourthR14pSX

/-- The representation of the image of the Fourth axis. -/
def fourthR14pL : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthR14pH, ShortData.ofList fourthR14pHT, 1 / 8,
    tensorRat 104 fourthR14pHX ((tensorWordDenAll fourthR14pH : ℚ) * 1)⟩

/-- The representation of the image of the Seventh representative. -/
def fourthR14pW : IdentVec :=
  ⟨(seventhSrcVecW 104).mat.act identSpatialAlphabet fourthR14pG, ShortData.ofList fourthR14pGT,
    (seventhSrcVecW 104).sden,
    tensorRat 104 fourthR14pGX ((tensorWordDenAll fourthR14pG : ℚ) * fourthR14pSD)⟩

set_option maxRecDepth 100000 in
/-- The plan of the source word expands to the source word. -/
theorem fourthR14pHP_word : planWord fourthR14pHP = fourthR14pH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word expands to the target word. -/
theorem fourthR14pGP_word : planWord fourthR14pGP = fourthR14pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of both plans are admissible. -/
theorem fourthR14pP_ok : planOk fourthR14pHP = true ∧ planOk fourthR14pGP = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem fourthR14pH_check :
    (fourthWordData fourthR14pH).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem fourthR14pG_check :
    (fourthWordData fourthR14pG).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fourthR14pD_ok : fourthR14pHD.ok = true ∧ fourthR14pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem fourthR14pHD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthR14pH).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthR14pHD.colsP i.val, fourthR14pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem fourthR14pGD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthR14pG).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthR14pGD.colsP i.val, fourthR14pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem fourthR14pHD_rows : ∀ i : Fin 24,
    fld 24 fourthR14pHD.rowsP i.val = rowsOf (fun j => fld 24 fourthR14pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem fourthR14pGD_rows : ∀ i : Fin 24,
    fld 24 fourthR14pGD.rowsP i.val = rowsOf (fun j => fld 24 fourthR14pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the Fourth image is transported onto the literal targets. -/
theorem fourthR14pHT_check : shortCheckF fourthR14pHD fourthSrcShort.flat fourthR14pHT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The target short list is the transport of the literal Seventh source short list. -/
theorem fourthR14p_wcheck :
    shortCheckF fourthR14pGD fourthSrcLit7Chunks.flatten fourthR14pGT = true := by
  have hl : fourthSrcLit7Chunks.length = fourthR14pGTChunks.length := by
    rw [fourthSrcLit7Chunks_length]
    rfl
  apply shortCheckF_flatten fourthR14pGD _ _ hl fourthR14p_wlens
  intro i hi
  rw [fourthSrcLit7Chunks_length] at hi
  interval_cases i
  · exact fourthR14p_wchunk0
  · exact fourthR14p_wchunk1
  · exact fourthR14p_wchunk2
  · exact fourthR14p_wchunk3
  · exact fourthR14p_wchunk4
  · exact fourthR14p_wchunk5
  · exact fourthR14p_wchunk6
  · exact fourthR14p_wchunk7
  · exact fourthR14p_wchunk8
  · exact fourthR14p_wchunk9
  · exact fourthR14p_wchunk10
  · exact fourthR14p_wchunk11
  · exact fourthR14p_wchunk12
  · exact fourthR14p_wchunk13
  · exact fourthR14p_wchunk14
  · exact fourthR14p_wchunk15
  · exact fourthR14p_wchunk16
  · exact fourthR14p_wchunk17
  · exact fourthR14p_wchunk18
  · exact fourthR14p_wchunk19
  · exact fourthR14p_wchunk20
  · exact fourthR14p_wchunk21
  · exact fourthR14p_wchunk22
  · exact fourthR14p_wchunk23
  · exact fourthR14p_wchunk24
  · exact fourthR14p_wchunk25
  · exact fourthR14p_wchunk26
  · exact fourthR14p_wchunk27
  · exact fourthR14p_wchunk28

/-- The short block of the Seventh image is transported onto the literal targets. -/
theorem fourthR14pGT_check :
    shortCheckF fourthR14pGD (seventhSrcVecW 104).sh.flat fourthR14pGT = true := by
  rw [fourthSrcLit7_eq]
  exact fourthR14p_wcheck

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem fourthR14pT_labels : fourthR14pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    fourthR14pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem fourthR14pH_growth : tensorWordGrowthAll fourthR14pH * 56 = 3670016 := by decide

/-- The word bound of the target word. -/
theorem fourthR14pG_growth :
    tensorWordGrowthAll fourthR14pG * (4 * (16777216 * 8) + 276 * 6144) =
      282364034940928 := by
  decide

/-- The tensor bound of the image of the Fourth axis. -/
theorem fourthR14pHX_bnd : TBnd 104 3670016 fourthR14pHX := by
  have h := (tensorPlanF_actual fourthR14pHP fourthR14pP_ok.1 (fourthSrcXW_bnd (w := 104) (by norm_num))
    (by rw [fourthR14pHP_word, fourthR14pH_growth]; norm_num) 1).1
  rw [fourthR14pHP_word, fourthR14pH_growth] at h
  exact h

/-- The tensor bound of the image of the Seventh representative. -/
theorem fourthR14pGX_bnd : TBnd 104 282364034940928 fourthR14pGX := by
  have h := (tensorPlanF_actual fourthR14pGP fourthR14pP_ok.2 (seventhSXF_bndB (w := 104) (by norm_num))
    (by rw [fourthR14pGP_word, fourthR14pG_growth]; norm_num) fourthR14pSD).1
  rw [fourthR14pGP_word, fourthR14pG_growth] at h
  exact h

/-- The coordinates of the Fourth image. -/
theorem fourthR14pL_actual : griessConwayEncode (rhoLocal (identWordLocal fourthR14pH)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthR14pL.real := by
  have hT := (tensorPlanF_actual fourthR14pHP fourthR14pP_ok.1 (fourthSrcXW_bnd (w := 104) (by norm_num))
    (by rw [fourthR14pHP_word, fourthR14pH_growth]; norm_num) 1).2
  rw [fourthR14pHP_word] at hT
  rw [← fourthWordData_fst fourthR14pH] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 104) (fourthWordData fourthR14pH) fourthR14pH_check
    fourthR14pHD fourthR14pD_ok.1 fourthR14pHD_cols fourthR14pHD_rows fourthR14pHT
    fourthR14pHT_check _ hT _ (fourthSrcW_rep (by norm_num))

/-- The coordinates of the Seventh image. -/
theorem fourthR14pW_actual : griessConwayEncode (rhoLocal (identWordLocal fourthR14pG)
    (generatedAxisGlobalTwelveRepresentative 6)) = fourthR14pW.real := by
  have hT := (tensorPlanF_actual fourthR14pGP fourthR14pP_ok.2 (seventhSXF_bndB (w := 104) (by norm_num))
    (by rw [fourthR14pGP_word, fourthR14pG_growth]; norm_num) fourthR14pSD).2
  rw [fourthR14pGP_word] at hT
  rw [show tensorRat 104 (seventhSXF 104) fourthR14pSD = (seventhSrcVecW 104).ten from
    seventhSXF104_ten] at hT
  rw [← fourthWordData_fst fourthR14pG] at hT ⊢
  exact IdentVec.word_actual (seventhSrcVecW 104) (fourthWordData fourthR14pG) fourthR14pG_check
    fourthR14pGD fourthR14pD_ok.2 fourthR14pGD_cols fourthR14pGD_rows fourthR14pGT
    fourthR14pGT_check _ hT _ (seventhSrcW_rep (by norm_num))

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
