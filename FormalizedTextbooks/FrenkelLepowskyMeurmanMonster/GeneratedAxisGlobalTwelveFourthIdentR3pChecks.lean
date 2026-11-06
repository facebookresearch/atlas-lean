/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR3pWShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSlices
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctGM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Data checks of the Fourth identification `R3p` (Twelfth target)

The source side is the image of the Fourth axis under the translated root word
(`fourthSrcVecW 64`), the target side the image of the Twelfth representative under the target
word (`twelfthSrcVecT 64`, worker `gforest`); both representations are computed by the word
actions and bound to the genuine coordinates here.  The packed tensors are evaluated by tensor
plans with fused monomial runs (`tensorPlanF`, gtenth); the Twelfth source tensor enters through
the kernel-feasible copy `twelfthSrcXW 64` with the same rational tensor.  The target short transport is
checked chunkwise. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor plan of the source word. -/
def fourthR3pHP : List TPlan :=
  [.letter (.xi),
    .run
      [(0, false), (1, false), (0, true)]
      [.trans 9 4, .trans 6 5, .trans 10 9, .trans 10 6, .trans 0 3, .trans 7 8, .trans 7 11,
        .trans 4 9, .trans 1 2, .trans 2 1, .trans 2 11, .trans 2 10, .trans 3 11,
        .trans 6 0, .trans 3 7, .trans 6 7, .trans 7 3, .trans 0 6, .trans 6 0,
        .trans 10 6, .trans 1 2, .trans 3 9, .trans 3 7, .trans 7 8, .trans 8 9,
        .trans 6 5, .trans 5 9, .trans 9 4],
    .letter (.xi),
    .run
      [(1, false)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6]]

/-- The tensor plan of the target word. -/
def fourthR3pGP : List TPlan :=
  [.letter (.qel (qmElt (10253170, true))),
    .run
      [(0, true), (0, true), (1, false), (0, false), (1, false), (0, false), (0, false),
        (1, false), (0, true), (0, true), (1, false), (0, false), (1, false), (0, false),
        (1, false), (0, true), (0, true), (1, false), (0, true), (1, false), (0, false),
        (1, true), (0, false), (1, true), (0, true), (0, true), (0, true), (1, true),
        (0, false), (0, false), (0, false), (1, true), (0, false), (1, true), (0, true),
        (1, true), (0, true), (0, true), (1, true), (0, true), (1, true), (0, false),
        (0, false), (0, false), (1, false), (0, true), (1, false), (0, true), (0, true),
        (0, true), (1, false), (0, true), (1, false), (0, false), (0, false), (1, false),
        (0, false), (0, false), (1, false), (0, true), (0, true), (1, false), (0, false),
        (0, false), (1, false), (0, false), (0, false)]
      [.trans 2 0, .trans 1 8, .trans 10 1, .trans 10 7, .trans 3 2, .trans 5 4, .trans 9 10,
        .trans 9 4, .trans 4 5, .trans 5 3, .trans 8 3, .trans 8 7, .trans 5 1,
        .trans 1 6, .trans 8 6, .trans 6 9, .trans 9 4, .trans 9 10, .trans 1 5,
        .trans 9 6, .trans 3 5, .trans 10 2, .trans 5 2, .trans 4 7, .trans 7 2,
        .trans 7 5, .trans 2 0, .trans 2 8, .trans 0 5, .trans 5 8, .trans 8 6,
        .trans 8 7, .trans 6 1, .trans 1 7, .trans 7 8, .trans 8 1, .trans 8 7],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, false), (1, true), (0, true), (1, true)]
      [.trans 0 4, .trans 6 2, .trans 0 7, .trans 0 3, .trans 3 6, .trans 9 10, .trans 5 1,
        .trans 9 7, .trans 3 11, .trans 7 5, .trans 10 0, .trans 7 11, .trans 2 3,
        .trans 8 9, .trans 2 0, .trans 3 5, .trans 8 4, .trans 1 5, .trans 5 3,
        .trans 1 0, .trans 6 0, .trans 5 2, .trans 2 8, .trans 8 7, .trans 0 1,
        .trans 0 3, .trans 8 2, .trans 0 5, .trans 8 5, .trans 7 10, .trans 10 9,
        .trans 9 1, .trans 1 11, .trans 4 6, .trans 6 9, .trans 9 4, .trans 9 6]]

/-- The packed tensor of the image of the Fourth axis. -/
def fourthR3pHX : List SVec := tensorPlanF 64 fourthR3pHP (fourthSrcXW 64)

/-- The packed tensor of the Twelfth source vector (kernel-feasible copy). -/
def fourthR3pSX : List SVec :=
  twelfthSrcXW 64

/-- The tensor denominator of the Twelfth source vector. -/
def fourthR3pSD : ℚ := 32

/-- The packed tensor of the image of the Twelfth representative. -/
def fourthR3pGX : List SVec := tensorPlanF 64 fourthR3pGP fourthR3pSX

/-- The representation of the image of the Fourth axis. -/
def fourthR3pL : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthR3pH, ShortData.ofList fourthR3pHT, 1 / 8,
    tensorRat 64 fourthR3pHX ((tensorWordDenAll fourthR3pH : ℚ) * 1)⟩

/-- The representation of the image of the Twelfth representative. -/
def fourthR3pW : IdentVec :=
  ⟨(twelfthSrcVecT 64).mat.act identSpatialAlphabet fourthR3pG, ShortData.ofList fourthR3pGT,
    (twelfthSrcVecT 64).sden,
    tensorRat 64 fourthR3pGX ((tensorWordDenAll fourthR3pG : ℚ) * fourthR3pSD)⟩

set_option maxRecDepth 100000 in
/-- The plan of the source word expands to the source word. -/
theorem fourthR3pHP_word : planWord fourthR3pHP = fourthR3pH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word expands to the target word. -/
theorem fourthR3pGP_word : planWord fourthR3pGP = fourthR3pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of both plans are admissible. -/
theorem fourthR3pP_ok : planOk fourthR3pHP = true ∧ planOk fourthR3pGP = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem fourthR3pH_check :
    (fourthWordData fourthR3pH).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem fourthR3pG_check :
    (fourthWordData fourthR3pG).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fourthR3pD_ok : fourthR3pHD.ok = true ∧ fourthR3pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem fourthR3pHD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthR3pH).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthR3pHD.colsP i.val, fourthR3pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem fourthR3pGD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthR3pG).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthR3pGD.colsP i.val, fourthR3pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem fourthR3pHD_rows : ∀ i : Fin 24,
    fld 24 fourthR3pHD.rowsP i.val = rowsOf (fun j => fld 24 fourthR3pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem fourthR3pGD_rows : ∀ i : Fin 24,
    fld 24 fourthR3pGD.rowsP i.val = rowsOf (fun j => fld 24 fourthR3pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the Fourth image is transported onto the literal targets. -/
theorem fourthR3pHT_check : shortCheckF fourthR3pHD fourthSrcShort.flat fourthR3pHT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The target short list is the transport of the literal Twelfth source short list. -/
theorem fourthR3p_wcheck :
    shortCheckF fourthR3pGD twelfthLitShort.flat fourthR3pGT = true := by
  have hl : (slices twelfthLitShort.flat [4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096]).length = fourthR3pGTChunks.length := by
    rw [slices_length]
    rfl
  have h := shortCheckF_flatten fourthR3pGD _ _ hl
    (fun i hi => fourthR3p_wlens i (by rw [slices_length] at hi; simpa using hi))
    (fun i hi => by
      rw [slices_length] at hi
      simp only [List.length_cons, List.length_nil] at hi
      interval_cases i
      · exact fourthR3p_wchunk0
      · exact fourthR3p_wchunk1
      · exact fourthR3p_wchunk2
      · exact fourthR3p_wchunk3
      · exact fourthR3p_wchunk4
      · exact fourthR3p_wchunk5
      · exact fourthR3p_wchunk6
      · exact fourthR3p_wchunk7
      · exact fourthR3p_wchunk8
      · exact fourthR3p_wchunk9
      · exact fourthR3p_wchunk10
      · exact fourthR3p_wchunk11)
  rwa [slices_flatten] at h

/-- The short block of the Twelfth image is transported onto the literal targets. -/
theorem fourthR3pGT_check :
    shortCheckF fourthR3pGD (twelfthSrcVecT 64).sh.flat fourthR3pGT = true := by
  exact fourthR3p_wcheck

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem fourthR3pT_labels : fourthR3pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    fourthR3pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem fourthR3pH_growth : tensorWordGrowthAll fourthR3pH * 56 = 3670016 := by decide

/-- The word bound of the target word. -/
theorem fourthR3pG_growth :
    tensorWordGrowthAll fourthR3pG * 15 =
      983040 := by
  decide

/-- The tensor bound of the image of the Fourth axis. -/
theorem fourthR3pHX_bnd : TBnd 64 3670016 fourthR3pHX := by
  have h := (tensorPlanF_actual fourthR3pHP fourthR3pP_ok.1 (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthR3pHP_word, fourthR3pH_growth]; norm_num) 1).1
  rw [fourthR3pHP_word, fourthR3pH_growth] at h
  exact h

/-- The tensor bound of the image of the Twelfth representative. -/
theorem fourthR3pGX_bnd : TBnd 64 983040 fourthR3pGX := by
  have h := (tensorPlanF_actual fourthR3pGP fourthR3pP_ok.2 (twelfthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthR3pGP_word, fourthR3pG_growth]; norm_num) fourthR3pSD).1
  rw [fourthR3pGP_word, fourthR3pG_growth] at h
  exact h

/-- The coordinates of the Fourth image. -/
theorem fourthR3pL_actual : griessConwayEncode (rhoLocal (identWordLocal fourthR3pH)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthR3pL.real := by
  have hT := (tensorPlanF_actual fourthR3pHP fourthR3pP_ok.1 (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthR3pHP_word, fourthR3pH_growth]; norm_num) 1).2
  rw [fourthR3pHP_word] at hT
  rw [← fourthWordData_fst fourthR3pH] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 64) (fourthWordData fourthR3pH) fourthR3pH_check
    fourthR3pHD fourthR3pD_ok.1 fourthR3pHD_cols fourthR3pHD_rows fourthR3pHT
    fourthR3pHT_check _ hT _ (fourthSrcW_rep (by norm_num))

/-- The coordinates of the Twelfth image. -/
theorem fourthR3pW_actual : griessConwayEncode (rhoLocal (identWordLocal fourthR3pG)
    (generatedAxisGlobalTwelveRepresentative 10)) = fourthR3pW.real := by
  have hT := (tensorPlanF_actual fourthR3pGP fourthR3pP_ok.2 (twelfthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthR3pGP_word, fourthR3pG_growth]; norm_num) fourthR3pSD).2
  rw [fourthR3pGP_word] at hT
  rw [← fourthWordData_fst fourthR3pG] at hT ⊢
  exact IdentVec.word_actual (twelfthSrcVecT 64) (fourthWordData fourthR3pG) fourthR3pG_check
    fourthR3pGD fourthR3pD_ok.2 fourthR3pGD_cols fourthR3pGD_rows fourthR3pGT
    fourthR3pGT_check _ hT _ (twelfthSrcT_rep (by norm_num))

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
