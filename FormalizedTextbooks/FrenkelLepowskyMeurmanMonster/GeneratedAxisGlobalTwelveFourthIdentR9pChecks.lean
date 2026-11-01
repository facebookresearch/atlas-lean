/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR9pWShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcEighth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSX8
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctGM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Data checks of the Fourth identification `R9p` (Eighth target)

The source side is the image of the Fourth axis under the translated root word
(`fourthSrcVecW 88`), the target side the image of the Eighth representative under the target
word (`eighthSrcVecW 88`, worker `gforest`); both representations are computed by the word
actions and bound to the genuine coordinates here.  The packed tensors are evaluated by tensor
plans with fused monomial runs (`tensorPlanF`, gtenth); the Eighth source tensor enters through
the kernel-feasible copy `eighthSXF 88` with the same rational tensor.  The target short transport is
checked chunkwise. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor plan of the source word. -/
def fourthR9pHP : List TPlan :=
  [.letter (.xi),
    .run
      [(1, false), (0, false)]
      [.trans 10 11, .trans 0 10, .trans 1 6, .trans 4 1, .trans 1 0, .trans 10 4, .trans 4 3,
        .trans 1 2, .trans 9 10, .trans 6 0, .trans 0 5, .trans 4 6, .trans 6 1,
        .trans 7 1, .trans 2 1, .trans 1 4, .trans 10 11, .trans 0 7, .trans 3 6,
        .trans 1 8, .trans 8 3, .trans 8 9, .trans 9 2, .trans 2 9, .trans 9 2,
        .trans 0 11, .trans 3 8, .trans 4 5, .trans 5 0, .trans 5 9, .trans 5 11,
        .trans 6 0, .trans 6 7, .trans 6 11, .trans 7 3, .trans 7 8, .trans 8 3,
        .trans 8 4, .trans 8 5, .trans 8 6, .trans 8 7, .trans 8 9],
    .letter (.xi),
    .run
      [(1, false)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6]]

/-- The tensor plan of the target word. -/
def fourthR9pGP : List TPlan :=
  [.letter (.qel (qmElt (12932809, true))),
    .letter (.sign 817 0),
    .run
      [(0, false), (0, false), (0, false), (1, false), (0, true), (0, true), (0, true),
        (1, false), (0, true), (1, false), (0, false), (0, false), (0, false),
        (1, false), (0, false), (1, false), (0, true), (0, true), (1, false), (0, false),
        (1, false), (0, false), (1, true), (0, false), (0, false), (0, false), (1, true),
        (0, false), (0, false), (1, true), (0, false), (1, true), (0, false), (0, false),
        (1, true), (0, true), (1, true), (0, true), (0, true), (1, true), (0, true),
        (0, true), (1, true), (0, false), (0, false), (1, false), (0, true), (1, false),
        (0, false), (0, false), (1, false), (0, false), (1, false), (0, false),
        (1, false), (0, true), (1, false), (0, true), (0, true), (0, true), (1, false),
        (0, true), (1, false), (0, false), (0, false), (1, false), (0, true), (0, true),
        (0, true)]
      [.trans 9 8, .trans 10 3, .trans 10 9, .trans 6 0, .trans 9 4, .trans 5 3, .trans 5 4,
        .trans 4 2, .trans 4 1, .trans 10 7, .trans 3 0, .trans 4 10, .trans 3 8,
        .trans 2 6, .trans 2 7, .trans 7 4, .trans 8 2, .trans 7 0, .trans 2 5,
        .trans 6 10, .trans 6 1, .trans 10 2, .trans 0 8, .trans 2 8, .trans 3 5,
        .trans 5 10, .trans 8 0, .trans 8 1, .trans 8 2, .trans 8 5, .trans 8 9,
        .trans 8 10, .trans 9 3, .trans 9 5, .trans 9 10, .trans 10 3, .trans 10 5,
        .trans 10 9],
    .letter (.xi),
    .letter (.xi)]

/-- The packed tensor of the image of the Fourth axis. -/
def fourthR9pHX : List SVec := tensorPlanF 88 fourthR9pHP (fourthSrcXW 88)

/-- The packed tensor of the Eighth source vector (kernel-feasible copy). -/
def fourthR9pSX : List SVec :=
  eighthSXF 88

/-- The tensor denominator of the Eighth source vector. -/
def fourthR9pSD : ℚ := (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The packed tensor of the image of the Eighth representative. -/
def fourthR9pGX : List SVec := tensorPlanF 88 fourthR9pGP fourthR9pSX

/-- The representation of the image of the Fourth axis. -/
def fourthR9pL : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthR9pH, ShortData.ofList fourthR9pHT, 1 / 8,
    tensorRat 88 fourthR9pHX ((tensorWordDenAll fourthR9pH : ℚ) * 1)⟩

/-- The representation of the image of the Eighth representative. -/
def fourthR9pW : IdentVec :=
  ⟨(eighthSrcVecW 88).mat.act identSpatialAlphabet fourthR9pG, ShortData.ofList fourthR9pGT,
    (eighthSrcVecW 88).sden,
    tensorRat 88 fourthR9pGX ((tensorWordDenAll fourthR9pG : ℚ) * fourthR9pSD)⟩

set_option maxRecDepth 100000 in
/-- The plan of the source word expands to the source word. -/
theorem fourthR9pHP_word : planWord fourthR9pHP = fourthR9pH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word expands to the target word. -/
theorem fourthR9pGP_word : planWord fourthR9pGP = fourthR9pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of both plans are admissible. -/
theorem fourthR9pP_ok : planOk fourthR9pHP = true ∧ planOk fourthR9pGP = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem fourthR9pH_check :
    (fourthWordData fourthR9pH).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem fourthR9pG_check :
    (fourthWordData fourthR9pG).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fourthR9pD_ok : fourthR9pHD.ok = true ∧ fourthR9pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem fourthR9pHD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthR9pH).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthR9pHD.colsP i.val, fourthR9pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem fourthR9pGD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthR9pG).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthR9pGD.colsP i.val, fourthR9pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem fourthR9pHD_rows : ∀ i : Fin 24,
    fld 24 fourthR9pHD.rowsP i.val = rowsOf (fun j => fld 24 fourthR9pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem fourthR9pGD_rows : ∀ i : Fin 24,
    fld 24 fourthR9pGD.rowsP i.val = rowsOf (fun j => fld 24 fourthR9pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the Fourth image is transported onto the literal targets. -/
theorem fourthR9pHT_check : shortCheckF fourthR9pHD fourthSrcShort.flat fourthR9pHT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The target short list is the transport of the literal Eighth source short list. -/
theorem fourthR9p_wcheck :
    shortCheckF fourthR9pGD fourthSrcLit8Chunks.flatten fourthR9pGT = true := by
  have hl : fourthSrcLit8Chunks.length = fourthR9pGTChunks.length := by
    rw [fourthSrcLit8Chunks_length]
    rfl
  apply shortCheckF_flatten fourthR9pGD _ _ hl fourthR9p_wlens
  intro i hi
  rw [fourthSrcLit8Chunks_length] at hi
  interval_cases i
  · exact fourthR9p_wchunk0
  · exact fourthR9p_wchunk1
  · exact fourthR9p_wchunk2
  · exact fourthR9p_wchunk3
  · exact fourthR9p_wchunk4
  · exact fourthR9p_wchunk5
  · exact fourthR9p_wchunk6
  · exact fourthR9p_wchunk7
  · exact fourthR9p_wchunk8
  · exact fourthR9p_wchunk9
  · exact fourthR9p_wchunk10
  · exact fourthR9p_wchunk11
  · exact fourthR9p_wchunk12
  · exact fourthR9p_wchunk13
  · exact fourthR9p_wchunk14
  · exact fourthR9p_wchunk15
  · exact fourthR9p_wchunk16
  · exact fourthR9p_wchunk17
  · exact fourthR9p_wchunk18
  · exact fourthR9p_wchunk19
  · exact fourthR9p_wchunk20
  · exact fourthR9p_wchunk21
  · exact fourthR9p_wchunk22
  · exact fourthR9p_wchunk23
  · exact fourthR9p_wchunk24
  · exact fourthR9p_wchunk25
  · exact fourthR9p_wchunk26
  · exact fourthR9p_wchunk27
  · exact fourthR9p_wchunk28
  · exact fourthR9p_wchunk29

/-- The short block of the Eighth image is transported onto the literal targets. -/
theorem fourthR9pGT_check :
    shortCheckF fourthR9pGD (eighthSrcVecW 88).sh.flat fourthR9pGT = true := by
  rw [fourthSrcLit8_eq]
  exact fourthR9p_wcheck

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem fourthR9pT_labels : fourthR9pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    fourthR9pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem fourthR9pH_growth : tensorWordGrowthAll fourthR9pH * 56 = 3670016 := by decide

/-- The word bound of the target word. -/
theorem fourthR9pG_growth :
    tensorWordGrowthAll fourthR9pG * (4 * (16777216 * 8) + 288 * 6144) =
      282402689646592 := by
  decide

/-- The tensor bound of the image of the Fourth axis. -/
theorem fourthR9pHX_bnd : TBnd 88 3670016 fourthR9pHX := by
  have h := (tensorPlanF_actual fourthR9pHP fourthR9pP_ok.1 (fourthSrcXW_bnd (w := 88) (by norm_num))
    (by rw [fourthR9pHP_word, fourthR9pH_growth]; norm_num) 1).1
  rw [fourthR9pHP_word, fourthR9pH_growth] at h
  exact h

/-- The tensor bound of the image of the Eighth representative. -/
theorem fourthR9pGX_bnd : TBnd 88 282402689646592 fourthR9pGX := by
  have h := (tensorPlanF_actual fourthR9pGP fourthR9pP_ok.2 (eighthSXF_bndB (w := 88) (by norm_num))
    (by rw [fourthR9pGP_word, fourthR9pG_growth]; norm_num) fourthR9pSD).1
  rw [fourthR9pGP_word, fourthR9pG_growth] at h
  exact h

/-- The coordinates of the Fourth image. -/
theorem fourthR9pL_actual : griessConwayEncode (rhoLocal (identWordLocal fourthR9pH)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthR9pL.real := by
  have hT := (tensorPlanF_actual fourthR9pHP fourthR9pP_ok.1 (fourthSrcXW_bnd (w := 88) (by norm_num))
    (by rw [fourthR9pHP_word, fourthR9pH_growth]; norm_num) 1).2
  rw [fourthR9pHP_word] at hT
  rw [← fourthWordData_fst fourthR9pH] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 88) (fourthWordData fourthR9pH) fourthR9pH_check
    fourthR9pHD fourthR9pD_ok.1 fourthR9pHD_cols fourthR9pHD_rows fourthR9pHT
    fourthR9pHT_check _ hT _ (fourthSrcW_rep (by norm_num))

/-- The coordinates of the Eighth image. -/
theorem fourthR9pW_actual : griessConwayEncode (rhoLocal (identWordLocal fourthR9pG)
    (generatedAxisGlobalTwelveRepresentative 7)) = fourthR9pW.real := by
  have hT := (tensorPlanF_actual fourthR9pGP fourthR9pP_ok.2 (eighthSXF_bndB (w := 88) (by norm_num))
    (by rw [fourthR9pGP_word, fourthR9pG_growth]; norm_num) fourthR9pSD).2
  rw [fourthR9pGP_word] at hT
  rw [show tensorRat 88 (eighthSXF 88) fourthR9pSD = (eighthSrcVecW 88).ten from
    eighthSXF88_ten] at hT
  rw [← fourthWordData_fst fourthR9pG] at hT ⊢
  exact IdentVec.word_actual (eighthSrcVecW 88) (fourthWordData fourthR9pG) fourthR9pG_check
    fourthR9pGD fourthR9pD_ok.2 fourthR9pGD_cols fourthR9pGD_rows fourthR9pGT
    fourthR9pGT_check _ hT _ (eighthSrcW_rep (by norm_num))

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
