/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcOddW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthRepresentative
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhWord

/-! # The Eighth local word applied to the Odd axis

The Eighth representative is `sExtra (L · v_Odd)` with the original seven-letter local word
`L = xi P1 P0 xi P1 P0 xi` (product order). This module gives an identification vector for the local
image `L · v_Odd` from `oddSrcVecW w`: matrix block by the spatial alphabet, short block by a
kernel-checked transport of the `552` Odd short terms onto a literal target list, tensor block by
the packed word action. The forward triality image of this vector is the Eighth source vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative
set_option autoImplicit false
set_option Elab.async false

/-- The Eighth local word with its letter data. -/
def srcEighthW : List (IdentLetter × QMaskP) :=
  [(.xi, sourceLetterP 0),
    (.mono (1, false), sourceLetterP (monoLetterIndex (1, false))),
    (.mono (0, false), sourceLetterP (monoLetterIndex (0, false))),
    (.xi, sourceLetterP 0),
    (.mono (1, false), sourceLetterP (monoLetterIndex (1, false))),
    (.mono (0, false), sourceLetterP (monoLetterIndex (0, false))),
    (.xi, sourceLetterP 0)]

/-- The Eighth local word. -/
def srcEighthH : List IdentLetter := srcEighthW.map Prod.fst

/-- Packed columns of `srcEighthD`. -/
@[irreducible] def srcEighthDCols : ℕ :=
    0x09a8f40964f6bc3cfd0f100e2ad0503f00f0d59a2c3f13609df2a1abe15f0063f63018f0 |||
    (0x90b987660f80010f040f3c00f03f0f5c9523913feae52abaa2d1e953e8e40740280ab9c <<< 288)

/-- Packed correction rows of `srcEighthD`. -/
@[irreducible] def srcEighthDRows : ℕ :=
    0xd1f00010f80002ac0001c200cb0e0005000048ed00040200b66f60a7ade8053a2004c220 |||
    (0xc00000000000d00000100000f200008800008c000004c00040e000 <<< 288)

/-- Packed composite mask data of the Eighth word. -/
def srcEighthD : QMaskP := ⟨srcEighthDCols, srcEighthDRows, 9204760⟩

/-- Packed labels (17-bit fields) of `srcEighthT`. -/
@[irreducible] def srcEighthTLabs : ℕ :=
    0xc29248b834c1189e8d6aa6b6c58a927aa8a8985ec3aea9d6acf7fbb9b86279e133108198 |||
    (0xaf3163529e40908bce8bc659625ab5fc366f703ed41ce232bd05870cd0d45c40c7b1ac08 <<< 288) |||
    (0x07cca0e660b39945dece04188cbb5458a33134578891e06aa2b074863b8d24762db35da9 <<< 576) |||
    (0x284db6e21e6695198c668d7690d7b1bb985ad89b0a3d8709368d75c6c629fc7501339ce9 <<< 864) |||
    (0xe02872c8baf513b50b418de90a766108f1fb186b4c366272c366913cdd90cec99aa64959 <<< 1152) |||
    (0x5715c04510f2c962ba70a4755799a81b940cc8f1e456f339622d10f85873ec259d2334c8 <<< 1440) |||
    (0x310dc807e86a23d9c2d0f8e46da03694099006a01159b66e5b7e99fe4aaa5e9d6c2a6627 <<< 1728) |||
    (0x4ad24667be46f93a30ed0736909547b58b39325b44b7e309e1fdf1de02a43075c6a8fdd1 <<< 2016) |||
    (0x215889d5a7ac0ec4415accf5793ab195583664ff4578469862b229de6ab85696ea439e5e <<< 2304) |||
    (0xf77d843180ad0cee819730422f9ddc32e1b97634bb643a089ef62371bb2232f46ea5da72 <<< 2592) |||
    (0x98811b224f5afb4d3dc9ddeb83e964fca9dcb47b2fa7942b4bb2a5c6effff6ff7dab7173 <<< 2880) |||
    (0xc4c748b32a6bd32e57172989589337029584ce06de72554e23c45b81cafaa45932a37153 <<< 3168) |||
    (0xa6d58046a1b530fc40033507ea1fa300aa70d9380aa0cd7d6c3a2f3c5b16e60d85c0234d <<< 3456) |||
    (0x4ecb67b0e07a4c0f80f727114a04e99b50412776d353f1c80bcc20777e75026ac36d612e <<< 3744) |||
    (0x939ed06cd1edaa06f5fb72f94f0d4b36c801720db3b80cf81b4c3b2100c70561bb278339 <<< 4032) |||
    (0xb854de0383e7683ba276d42cfcd82007cbb60e5fd220fc7777405345dda4f9f410cbbc49 <<< 4320) |||
    (0x5ffe552ca964243073c8c17f40a42168ec900c0e9e07ef0223873470871dc2d0e6a6406d <<< 4608) |||
    (0xb94f5b47da06e41da99544f2a330190770cb3c123c247e185b2d5bc19bc3179da42cc08c <<< 4896) |||
    (0x0282ccc6120a329f506a83354610cb53f524a8c525696ab0535817b5585a53aaad797c5e <<< 5184) |||
    (0x38f454b50ba38db922566114f1f5386e5434ee71e566e15f3b2b4756b3aba5d924ddb5ad <<< 5472) |||
    (0x57ca194a3e4308d68da546ae69ee550615e9f29aed6caab995990ddeba6328c2f0286fda <<< 5760) |||
    (0xfb451f92cb816650944c42e63291e236900467062a7e461da235f68c36a54d44e9b1c198 <<< 6048) |||
    (0x3167fee40530ae8460431187647a39dedeff6a90aa6f82ac7a9bc75ae059062895ab6bea <<< 6336) |||
    (0xada80cb4098892eb360514ba940f4b1b9da92ca667710b291d0e8cfcc46e98a14f9ef34e <<< 6624) |||
    (0xe3d68dabfcd60186769444391f428553a6531075a769aa50f3f0ecf8f691aabf5da0a3d1 <<< 6912) |||
    (0x225bbddbfdef00d721ab8f238131ff389f42aa171ea6ec7acbed320aed82e6aca4a29dae <<< 7200) |||
    (0x7c6b33955ccb14976ed27bf9817ca79e5430f8d27380df7d8c3f7699d5cd995bf6e5d374 <<< 7488) |||
    (0xa0a5f1234924df48daef2b847ac2a7b5e38489f8583a24d0123a06eb1362626bac87356b <<< 7776) |||
    (0x4018a5f65e1be8049408420bbd57c6033bf5f1ca4c9469702e1b49bdcd87858fa33f01a0 <<< 8064) |||
    (0x601b8843dddcb013e57721bea10406e06257ddf872901248112876e4050a5db66fb140ff <<< 8352) |||
    (0xefd7205e63b03c320aec277b56074f00e1ef6970c9cb6ec018fedbcb808701ff03c7f015 <<< 8640) |||
    (0x4202eef010a7ebbc6df35816526c0503d1dafe6feda012ec1d1c781cefef4d9e8882df32 <<< 8928) |||
    (0x70d8010edcb0ae1cb109db95b60dfc9b9278aa8f10 <<< 9216)

/-- Packed numerators (8-bit fields, offset 128) of `srcEighthT`. -/
@[irreducible] def srcEighthTNums : ℕ :=
    0x7f81817f818181817f81818181837d83838383837d7d7d8383837d7d7d7d83838383837d |||
    (0x8181817f7f817f817f8181817f7f817f81817f7f8181817f7f81817f8181817f7f817f7f <<< 288) |||
    (0x7f7f817f817f817f7f7f7f8181817f817f817f7f817f817f7f817f7f7f7f7f8181818181 <<< 576) |||
    (0x817f7f7f7f7f7f817f818181818181817f8181817f7f817f817f7f7f7f81817f817f8181 <<< 864) |||
    (0x7f81817f7f8181817f817f81818181817f7f7f7f7f817f817f7f7f817f8181817f7f7f7f <<< 1152) |||
    (0x7f817f81817f817f817f7f817f817f7f7f817f7f81817f7f7f7f8181817f817f7f817f81 <<< 1440) |||
    (0x7f7f7f81817f81817f8181818181817f8181817f7f817f7f8181817f7f7f7f7f7f818181 <<< 1728) |||
    (0x7d7d837d83837d7d837d7d7d7f7f81817f7f7f81817f7f817f81817f7f81817f7f7f7f7f <<< 2016) |||
    (0x81817f818181817f81817f81817f817f817f81817f817f818183837d7d7d837d837d7d83 <<< 2304) |||
    (0x817f817f81817f81817f7f7f817f7f8181817f7f817f7f818181817f817f8181817f7f81 <<< 2592) |||
    (0x7f817f818181817f7f817f8181817f81817f817f817f7f7f7f7f7f817f7f7f7f817f8181 <<< 2880) |||
    (0x7f81817f81817f7f7f7f7f817f817f817f81817f81817f7f8181817f817f817f817f7f81 <<< 3168) |||
    (0x8181818181817f817f817f8181818181817f81817f81817f7f7f817f817f7f7f817f8181 <<< 3456) |||
    (0x81817f7f7f81817f817f7f7f7f7f8181817f81817f818181817f7f7f7f7f7f817f7f817f <<< 3744) |||
    (0x7f81817f817f7f817f7f818181817f7f7f7f81817f7f81817f81817f817f817f817f7f7f <<< 4032) |||
    (0x7f7f7f8181817f7f7f818181 <<< 4320)

/-- The transported short list `srcEighthT` (552 terms, source order). -/
def srcEighthT : List (ℕ × ℤ) := srcDecodeTerms srcEighthTLabs srcEighthTNums 552

/-! ## Checks of the literal data -/

set_option maxRecDepth 100000 in
/-- The letter data of the Eighth word are certified. -/
theorem srcEighthW_check : srcEighthW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem srcEighthD_ok : srcEighthD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem srcEighthD_cols : ∀ i : Fin 24, qmWordP (srcEighthW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 srcEighthD.colsP i.val, srcEighthD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem srcEighthD_rows : ∀ i : Fin 24,
    fld 24 srcEighthD.rowsP i.val = rowsOf (fun j => fld 24 srcEighthD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The Odd short block is transported onto the literal target list. -/
theorem srcEighthT_check : shortCheckF srcEighthD oddSrcShort.flat srcEighthT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The target list has valid labels. -/
theorem srcEighthT_labels : srcEighthT.all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-! ## The local image -/

/-- The field-bound growth of the Eighth word (three Xi letters). -/
theorem srcEighthH_growth : tensorWordGrowthAll srcEighthH = 16777216 := by decide

/-- The tensor denominator of the Eighth word. -/
theorem srcEighthH_den : tensorWordDenAll srcEighthH = 4096 := by decide

/-- The packed tensor of `L · v_Odd` at width `w` (numerators over `4096`). -/
def srcEighthYX (w : ℕ) : List SVec := tensorWordAll w srcEighthH (oddSrcXW w)

/-- The identification vector of `L · v_Odd` at width `w`. -/
def srcEighthY (w : ℕ) : IdentVec :=
  ⟨oddSrcMat.act identSpatialAlphabet srcEighthH, ShortData.ofList srcEighthT, 1 / 4,
    tensorRat w (srcEighthYX w) ((tensorWordDenAll srcEighthH : ℚ) * 1)⟩

/-- Bounds of the packed tensor of `L · v_Odd`. -/
theorem srcEighthH_bound {w : ℕ} (hw : 28 ≤ w) : tensorWordGrowthAll srcEighthH * 8 < 2 ^ w := by
  rw [srcEighthH_growth]
  calc 16777216 * 8 < 2 ^ 28 := by norm_num
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw

/-- Bounds of the packed tensor of `L · v_Odd`. -/
theorem srcEighthYX_bnd {w : ℕ} (hw : 28 ≤ w) : TBnd w (16777216 * 8) (srcEighthYX w) := by
  have h := (tensorWordAll_actual srcEighthH (oddSrcXW_bnd (w := w) (by omega))
    (srcEighthH_bound hw) 1).1
  rw [srcEighthH_growth] at h
  exact h

/-- The coordinates of `L · v_Odd`. -/
theorem srcEighthY_actual {w : ℕ} (hw : 28 ≤ w) : griessConwayEncode (rhoLocal
    (identWordLocal srcEighthH) (generatedAxisGlobalTwelveRepresentative 2)) =
      (srcEighthY w).real :=
  IdentVec.word_actual (oddSrcVecW w) srcEighthW srcEighthW_check srcEighthD srcEighthD_ok
    srcEighthD_cols srcEighthD_rows srcEighthT srcEighthT_check _
    (tensorWordAll_actual srcEighthH (oddSrcXW_bnd (w := w) (by omega))
      (srcEighthH_bound hw) 1).2 _ (oddSrcW_rep (by omega))

/-- The Eighth word is the original local factor of the Eighth representative. -/
theorem srcEighthH_local :
    identWordLocal srcEighthH = localFiberIntoH generatedEighthLocalFiber := by
  rw [identWordLocal]
  refine congrArg localFiberIntoH ?_
  change xiSpinLocalFiber * (generatedFourthMonomialFiberLetter (1, false) *
      (generatedFourthMonomialFiberLetter (0, false) * (xiSpinLocalFiber *
      (generatedFourthMonomialFiberLetter (1, false) *
      (generatedFourthMonomialFiberLetter (0, false) *
      (xiSpinLocalFiber * 1)))))) = generatedEighthLocalFiber
  simp only [generatedFourthMonomialFiberLetter, Bool.false_eq_true, ↓reduceIte, mul_one,
    generatedEighthLocalFiber, mul_assoc]

/-- The Eighth representative is the forward triality image of `L · v_Odd`. -/
theorem srcEighth_rep_eq : generatedAxisGlobalTwelveRepresentative 7 =
    sExtra (rhoLocal (identWordLocal srcEighthH)
      (generatedAxisGlobalTwelveRepresentative 2)) := by
  rw [srcEighthH_local]
  rfl

/-- The short block of `L · v_Odd` satisfies the range conditions. -/
theorem srcEighthY_ok (w : ℕ) : (srcEighthY w).sh.ok = true :=
  ofList_ok srcEighthT srcEighthT_labels

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
