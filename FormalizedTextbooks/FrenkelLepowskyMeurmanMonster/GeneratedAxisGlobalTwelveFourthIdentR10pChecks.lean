/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR10pWShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSixthW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSX6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctGM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Data checks of the Fourth identification `R10p` (Sixth target)

The source side is the image of the Fourth axis under the translated root word
(`fourthSrcVecW 88`), the target side the image of the Sixth representative under the target
word (`sixthSrcVecW 88`, worker `gforest`); both representations are computed by the word
actions and bound to the genuine coordinates here.  The packed tensors are evaluated by tensor
plans with fused monomial runs (`tensorPlanF`, gtenth); the Sixth source tensor enters through
the kernel-feasible copy `sixthSXF 88` with the same rational tensor.  The target short transport is
checked chunkwise. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor plan of the source word. -/
def fourthR10pHP : List TPlan :=
  [.letter (.xi),
    .run
      [(1, false)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6],
    .letter (.xi),
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
def fourthR10pGP : List TPlan :=
  [.letter (.qel (qmElt (11882499, false))),
    .letter (.sign 1890 0),
    .run
      [(1, false), (0, false), (0, false), (1, false), (0, true), (1, false), (0, true),
        (0, true), (1, false), (0, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
        (0, true), (0, true), (1, false), (0, true), (0, true), (1, false), (0, true),
        (1, false), (0, false), (0, false), (1, true), (0, false), (0, false), (1, true),
        (0, true), (1, true), (0, true), (1, true), (0, false), (0, false), (1, true),
        (0, false), (1, true), (0, true), (1, true), (0, true), (1, true), (0, false),
        (0, false), (1, true), (0, false), (0, false), (1, true), (0, false), (0, false),
        (1, false), (0, false), (0, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, false), (0, false), (1, false), (0, false),
        (1, false), (0, true), (1, false), (0, false), (1, false), (0, false),
        (1, false), (0, true), (0, true), (1, false)]
      [.trans 2 1, .trans 0 2, .trans 0 3, .trans 1 3, .trans 5 0, .trans 10 4, .trans 8 1,
        .trans 7 5, .trans 5 7, .trans 7 5, .trans 10 7, .trans 3 2, .trans 6 2,
        .trans 5 1, .trans 9 2, .trans 2 3, .trans 6 4, .trans 4 6, .trans 6 4,
        .trans 3 1, .trans 1 2, .trans 6 0],
    .letter (.xi),
    .letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6]]

/-- The packed tensor of the image of the Fourth axis. -/
def fourthR10pHX : List SVec := tensorPlanF 88 fourthR10pHP (fourthSrcXW 88)

/-- The packed tensor of the Sixth source vector (kernel-feasible copy). -/
def fourthR10pSX : List SVec :=
  sixthSXF 88

/-- The tensor denominator of the Sixth source vector. -/
def fourthR10pSD : ℚ := 32

/-- The packed tensor of the image of the Sixth representative. -/
def fourthR10pGX : List SVec := tensorPlanF 88 fourthR10pGP fourthR10pSX

/-- The representation of the image of the Fourth axis. -/
def fourthR10pL : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthR10pH, ShortData.ofList fourthR10pHT, 1 / 8,
    tensorRat 88 fourthR10pHX ((tensorWordDenAll fourthR10pH : ℚ) * 1)⟩

/-- The representation of the image of the Sixth representative. -/
def fourthR10pW : IdentVec :=
  ⟨(sixthSrcVecW 88).mat.act identSpatialAlphabet fourthR10pG, ShortData.ofList fourthR10pGT,
    (sixthSrcVecW 88).sden,
    tensorRat 88 fourthR10pGX ((tensorWordDenAll fourthR10pG : ℚ) * fourthR10pSD)⟩

set_option maxRecDepth 100000 in
/-- The plan of the source word expands to the source word. -/
theorem fourthR10pHP_word : planWord fourthR10pHP = fourthR10pH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word expands to the target word. -/
theorem fourthR10pGP_word : planWord fourthR10pGP = fourthR10pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of both plans are admissible. -/
theorem fourthR10pP_ok : planOk fourthR10pHP = true ∧ planOk fourthR10pGP = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem fourthR10pH_check :
    (fourthWordData fourthR10pH).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem fourthR10pG_check :
    (fourthWordData fourthR10pG).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fourthR10pD_ok : fourthR10pHD.ok = true ∧ fourthR10pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem fourthR10pHD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthR10pH).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthR10pHD.colsP i.val, fourthR10pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem fourthR10pGD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthR10pG).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthR10pGD.colsP i.val, fourthR10pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem fourthR10pHD_rows : ∀ i : Fin 24,
    fld 24 fourthR10pHD.rowsP i.val = rowsOf (fun j => fld 24 fourthR10pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem fourthR10pGD_rows : ∀ i : Fin 24,
    fld 24 fourthR10pGD.rowsP i.val = rowsOf (fun j => fld 24 fourthR10pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the Fourth image is transported onto the literal targets. -/
theorem fourthR10pHT_check : shortCheckF fourthR10pHD fourthSrcShort.flat fourthR10pHT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The target short list is the transport of the literal Sixth source short list. -/
theorem fourthR10p_wcheck :
    shortCheckF fourthR10pGD fourthSrcLit6Chunks.flatten fourthR10pGT = true := by
  have hl : fourthSrcLit6Chunks.length = fourthR10pGTChunks.length := by
    rw [fourthSrcLit6Chunks_length]
    rfl
  apply shortCheckF_flatten fourthR10pGD _ _ hl fourthR10p_wlens
  intro i hi
  rw [fourthSrcLit6Chunks_length] at hi
  interval_cases i
  · exact fourthR10p_wchunk0
  · exact fourthR10p_wchunk1
  · exact fourthR10p_wchunk2
  · exact fourthR10p_wchunk3
  · exact fourthR10p_wchunk4
  · exact fourthR10p_wchunk5
  · exact fourthR10p_wchunk6
  · exact fourthR10p_wchunk7
  · exact fourthR10p_wchunk8

/-- The short block of the Sixth image is transported onto the literal targets. -/
theorem fourthR10pGT_check :
    shortCheckF fourthR10pGD (sixthSrcVecW 88).sh.flat fourthR10pGT = true := by
  rw [fourthSrcLit6_eq]
  exact fourthR10p_wcheck

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem fourthR10pT_labels : fourthR10pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    fourthR10pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem fourthR10pH_growth : tensorWordGrowthAll fourthR10pH * 56 = 939524096 := by decide

/-- The word bound of the target word. -/
theorem fourthR10pG_growth :
    tensorWordGrowthAll fourthR10pG * (4096 * 64) =
      137438953472 := by
  decide

/-- The tensor bound of the image of the Fourth axis. -/
theorem fourthR10pHX_bnd : TBnd 88 939524096 fourthR10pHX := by
  have h := (tensorPlanF_actual fourthR10pHP fourthR10pP_ok.1 (fourthSrcXW_bnd (w := 88) (by norm_num))
    (by rw [fourthR10pHP_word, fourthR10pH_growth]; norm_num) 1).1
  rw [fourthR10pHP_word, fourthR10pH_growth] at h
  exact h

/-- The tensor bound of the image of the Sixth representative. -/
theorem fourthR10pGX_bnd : TBnd 88 137438953472 fourthR10pGX := by
  have h := (tensorPlanF_actual fourthR10pGP fourthR10pP_ok.2 (sixthSXF_bnd64 (w := 88) (by norm_num))
    (by rw [fourthR10pGP_word, fourthR10pG_growth]; norm_num) fourthR10pSD).1
  rw [fourthR10pGP_word, fourthR10pG_growth] at h
  exact h

/-- The coordinates of the Fourth image. -/
theorem fourthR10pL_actual : griessConwayEncode (rhoLocal (identWordLocal fourthR10pH)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthR10pL.real := by
  have hT := (tensorPlanF_actual fourthR10pHP fourthR10pP_ok.1 (fourthSrcXW_bnd (w := 88) (by norm_num))
    (by rw [fourthR10pHP_word, fourthR10pH_growth]; norm_num) 1).2
  rw [fourthR10pHP_word] at hT
  rw [← fourthWordData_fst fourthR10pH] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 88) (fourthWordData fourthR10pH) fourthR10pH_check
    fourthR10pHD fourthR10pD_ok.1 fourthR10pHD_cols fourthR10pHD_rows fourthR10pHT
    fourthR10pHT_check _ hT _ (fourthSrcW_rep (by norm_num))

/-- The coordinates of the Sixth image. -/
theorem fourthR10pW_actual : griessConwayEncode (rhoLocal (identWordLocal fourthR10pG)
    (generatedAxisGlobalTwelveRepresentative 5)) = fourthR10pW.real := by
  have hT := (tensorPlanF_actual fourthR10pGP fourthR10pP_ok.2 (sixthSXF_bnd64 (w := 88) (by norm_num))
    (by rw [fourthR10pGP_word, fourthR10pG_growth]; norm_num) fourthR10pSD).2
  rw [fourthR10pGP_word] at hT
  rw [show tensorRat 88 (sixthSXF 88) fourthR10pSD = (sixthSrcVecW 88).ten from
    sixthSXF_ten (w := 88) (by norm_num)] at hT
  rw [← fourthWordData_fst fourthR10pG] at hT ⊢
  exact IdentVec.word_actual (sixthSrcVecW 88) (fourthWordData fourthR10pG) fourthR10pG_check
    fourthR10pGD fourthR10pD_ok.2 fourthR10pGD_cols fourthR10pGD_rows fourthR10pGT
    fourthR10pGT_check _ hT _ (sixthSrcW_rep (by norm_num))

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
