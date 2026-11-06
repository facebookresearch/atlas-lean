/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14nWShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSixthW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSX6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctGM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Data checks of the Fourth identification `R14n` (Sixth target)

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
def fourthR14nHP : List TPlan :=
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
def fourthR14nGP : List TPlan :=
  [.letter (.qel (qmElt (766944, false))),
    .letter (.sign 926 0),
    .run
      [(0, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
        (0, false), (0, false), (1, false), (0, false), (0, false), (1, false),
        (0, true), (1, false), (0, true), (0, true), (1, false), (0, true), (1, false),
        (0, false), (1, false), (0, true), (0, true), (1, true), (0, false), (1, true),
        (0, false), (0, false), (0, false), (1, true), (0, true), (0, true), (1, true),
        (0, false), (0, false), (1, true), (0, false), (0, false), (1, true), (0, true),
        (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (0, true),
        (1, false), (0, false), (0, false), (1, false), (0, false), (1, false),
        (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false),
        (1, false), (0, false), (1, false), (0, false), (0, false), (0, false)]
      [.trans 4 6, .trans 6 1, .trans 3 4, .trans 6 0, .trans 10 3, .trans 7 10, .trans 5 0,
        .trans 1 3, .trans 2 9, .trans 2 4, .trans 5 11, .trans 0 5, .trans 9 6,
        .trans 8 6, .trans 0 3, .trans 3 8, .trans 1 5, .trans 8 2, .trans 2 8,
        .trans 3 4, .trans 3 11, .trans 4 1, .trans 4 5, .trans 5 1, .trans 5 4,
        .trans 5 9, .trans 6 9, .trans 7 2, .trans 7 6, .trans 7 9, .trans 8 3,
        .trans 8 5, .trans 8 9, .trans 8 11, .trans 9 2, .trans 9 10, .trans 10 3,
        .trans 10 5, .trans 10 6, .trans 10 7, .trans 10 8],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, false), (0, false), (1, true)]
      [.trans 10 0, .trans 6 11, .trans 5 3, .trans 0 4, .trans 0 7, .trans 7 6, .trans 6 1,
        .trans 1 2, .trans 10 5, .trans 4 10, .trans 8 7, .trans 7 9, .trans 9 10,
        .trans 9 5, .trans 10 8, .trans 6 11, .trans 7 3, .trans 5 0, .trans 6 0,
        .trans 0 8, .trans 0 4, .trans 3 2, .trans 2 1, .trans 1 9, .trans 9 7,
        .trans 1 8, .trans 8 10, .trans 10 3, .trans 10 2, .trans 8 11, .trans 10 7,
        .trans 8 6, .trans 7 5, .trans 2 4, .trans 4 0, .trans 4 6, .trans 6 5,
        .trans 0 3, .trans 3 11]]

/-- The packed tensor of the image of the Fourth axis. -/
def fourthR14nHX : List SVec := tensorPlanF 88 fourthR14nHP (fourthSrcXW 88)

/-- The packed tensor of the Sixth source vector (kernel-feasible copy). -/
def fourthR14nSX : List SVec :=
  sixthSXF 88

/-- The tensor denominator of the Sixth source vector. -/
def fourthR14nSD : ℚ := 32

/-- The packed tensor of the image of the Sixth representative. -/
def fourthR14nGX : List SVec := tensorPlanF 88 fourthR14nGP fourthR14nSX

/-- The representation of the image of the Fourth axis. -/
def fourthR14nL : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthR14nH, ShortData.ofList fourthR14nHT, 1 / 8,
    tensorRat 88 fourthR14nHX ((tensorWordDenAll fourthR14nH : ℚ) * 1)⟩

/-- The representation of the image of the Sixth representative. -/
def fourthR14nW : IdentVec :=
  ⟨(sixthSrcVecW 88).mat.act identSpatialAlphabet fourthR14nG, ShortData.ofList fourthR14nGT,
    (sixthSrcVecW 88).sden,
    tensorRat 88 fourthR14nGX ((tensorWordDenAll fourthR14nG : ℚ) * fourthR14nSD)⟩

set_option maxRecDepth 100000 in
/-- The plan of the source word expands to the source word. -/
theorem fourthR14nHP_word : planWord fourthR14nHP = fourthR14nH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word expands to the target word. -/
theorem fourthR14nGP_word : planWord fourthR14nGP = fourthR14nG := rfl

set_option maxRecDepth 100000 in
/-- The runs of both plans are admissible. -/
theorem fourthR14nP_ok : planOk fourthR14nHP = true ∧ planOk fourthR14nGP = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem fourthR14nH_check :
    (fourthWordData fourthR14nH).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem fourthR14nG_check :
    (fourthWordData fourthR14nG).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fourthR14nD_ok : fourthR14nHD.ok = true ∧ fourthR14nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem fourthR14nHD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthR14nH).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthR14nHD.colsP i.val, fourthR14nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem fourthR14nGD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthR14nG).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthR14nGD.colsP i.val, fourthR14nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem fourthR14nHD_rows : ∀ i : Fin 24,
    fld 24 fourthR14nHD.rowsP i.val = rowsOf (fun j => fld 24 fourthR14nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem fourthR14nGD_rows : ∀ i : Fin 24,
    fld 24 fourthR14nGD.rowsP i.val = rowsOf (fun j => fld 24 fourthR14nGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the Fourth image is transported onto the literal targets. -/
theorem fourthR14nHT_check : shortCheckF fourthR14nHD fourthSrcShort.flat fourthR14nHT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The target short list is the transport of the literal Sixth source short list. -/
theorem fourthR14n_wcheck :
    shortCheckF fourthR14nGD fourthSrcLit6Chunks.flatten fourthR14nGT = true := by
  have hl : fourthSrcLit6Chunks.length = fourthR14nGTChunks.length := by
    rw [fourthSrcLit6Chunks_length]
    rfl
  apply shortCheckF_flatten fourthR14nGD _ _ hl fourthR14n_wlens
  intro i hi
  rw [fourthSrcLit6Chunks_length] at hi
  interval_cases i
  · exact fourthR14n_wchunk0
  · exact fourthR14n_wchunk1
  · exact fourthR14n_wchunk2
  · exact fourthR14n_wchunk3
  · exact fourthR14n_wchunk4
  · exact fourthR14n_wchunk5
  · exact fourthR14n_wchunk6
  · exact fourthR14n_wchunk7
  · exact fourthR14n_wchunk8

/-- The short block of the Sixth image is transported onto the literal targets. -/
theorem fourthR14nGT_check :
    shortCheckF fourthR14nGD (sixthSrcVecW 88).sh.flat fourthR14nGT = true := by
  rw [fourthSrcLit6_eq]
  exact fourthR14n_wcheck

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem fourthR14nT_labels : fourthR14nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    fourthR14nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem fourthR14nH_growth : tensorWordGrowthAll fourthR14nH * 56 = 3670016 := by decide

/-- The word bound of the target word. -/
theorem fourthR14nG_growth :
    tensorWordGrowthAll fourthR14nG * (4096 * 64) =
      137438953472 := by
  decide

/-- The tensor bound of the image of the Fourth axis. -/
theorem fourthR14nHX_bnd : TBnd 88 3670016 fourthR14nHX := by
  have h := (tensorPlanF_actual fourthR14nHP fourthR14nP_ok.1 (fourthSrcXW_bnd (w := 88) (by norm_num))
    (by rw [fourthR14nHP_word, fourthR14nH_growth]; norm_num) 1).1
  rw [fourthR14nHP_word, fourthR14nH_growth] at h
  exact h

/-- The tensor bound of the image of the Sixth representative. -/
theorem fourthR14nGX_bnd : TBnd 88 137438953472 fourthR14nGX := by
  have h := (tensorPlanF_actual fourthR14nGP fourthR14nP_ok.2 (sixthSXF_bnd64 (w := 88) (by norm_num))
    (by rw [fourthR14nGP_word, fourthR14nG_growth]; norm_num) fourthR14nSD).1
  rw [fourthR14nGP_word, fourthR14nG_growth] at h
  exact h

/-- The coordinates of the Fourth image. -/
theorem fourthR14nL_actual : griessConwayEncode (rhoLocal (identWordLocal fourthR14nH)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthR14nL.real := by
  have hT := (tensorPlanF_actual fourthR14nHP fourthR14nP_ok.1 (fourthSrcXW_bnd (w := 88) (by norm_num))
    (by rw [fourthR14nHP_word, fourthR14nH_growth]; norm_num) 1).2
  rw [fourthR14nHP_word] at hT
  rw [← fourthWordData_fst fourthR14nH] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 88) (fourthWordData fourthR14nH) fourthR14nH_check
    fourthR14nHD fourthR14nD_ok.1 fourthR14nHD_cols fourthR14nHD_rows fourthR14nHT
    fourthR14nHT_check _ hT _ (fourthSrcW_rep (by norm_num))

/-- The coordinates of the Sixth image. -/
theorem fourthR14nW_actual : griessConwayEncode (rhoLocal (identWordLocal fourthR14nG)
    (generatedAxisGlobalTwelveRepresentative 5)) = fourthR14nW.real := by
  have hT := (tensorPlanF_actual fourthR14nGP fourthR14nP_ok.2 (sixthSXF_bnd64 (w := 88) (by norm_num))
    (by rw [fourthR14nGP_word, fourthR14nG_growth]; norm_num) fourthR14nSD).2
  rw [fourthR14nGP_word] at hT
  rw [show tensorRat 88 (sixthSXF 88) fourthR14nSD = (sixthSrcVecW 88).ten from
    sixthSXF_ten (w := 88) (by norm_num)] at hT
  rw [← fourthWordData_fst fourthR14nG] at hT ⊢
  exact IdentVec.word_actual (sixthSrcVecW 88) (fourthWordData fourthR14nG) fourthR14nG_check
    fourthR14nGD fourthR14nD_ok.2 fourthR14nGD_cols fourthR14nGD_rows fourthR14nGT
    fourthR14nGT_check _ hT _ (sixthSrcW_rep (by norm_num))

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
