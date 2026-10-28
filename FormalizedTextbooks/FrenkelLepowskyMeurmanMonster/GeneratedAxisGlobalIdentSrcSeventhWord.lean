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
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhRepresentative

/-! # The Seventh local word applied to the Odd axis

The Seventh representative is `sExtra (L · v_Odd)` with the original seven-letter local word
`L = xi P1 xi P0 P1 P0 xi` (product order). This module gives an identification vector for the local
image `L · v_Odd` from `oddSrcVecW w`: matrix block by the spatial alphabet, short block by a
kernel-checked transport of the `552` Odd short terms onto a literal target list, tensor block by
the packed word action. The forward triality image of this vector is the Seventh source vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative
set_option autoImplicit false
set_option Elab.async false

/-- Decode packed terms: labels in 17-bit fields, numerators in 8-bit fields with offset 128. -/
def srcDecodeTerms (labs nums : ℕ) : ℕ → List (ℕ × ℤ)
  | 0 => []
  | n + 1 => ((labs &&& 131071 : ℕ), ((nums &&& 255 : ℕ) : ℤ) - 128) ::
      srcDecodeTerms (labs >>> 17) (nums >>> 8) n

/-- The Seventh local word with its letter data. -/
def srcSeventhW : List (IdentLetter × QMaskP) :=
  [(.xi, sourceLetterP 0),
    (.mono (1, false), sourceLetterP (monoLetterIndex (1, false))),
    (.xi, sourceLetterP 0),
    (.mono (0, false), sourceLetterP (monoLetterIndex (0, false))),
    (.mono (1, false), sourceLetterP (monoLetterIndex (1, false))),
    (.mono (0, false), sourceLetterP (monoLetterIndex (0, false))),
    (.xi, sourceLetterP 0)]

/-- The Seventh local word. -/
def srcSeventhH : List IdentLetter := srcSeventhW.map Prod.fst

/-- Packed columns of `srcSeventhD`. -/
@[irreducible] def srcSeventhDCols : ℕ :=
    0x89abf2b9b40083c7c10f00feba0ef00f030025f7783f109032eaa134f95fb063fe301bf2 |||
    (0xf66066c963fe0f100e3cf80f3f03f02ad15e0913fe814aaf2afb4215eb22300cf6f01398 <<< 288)

/-- Packed correction rows of `srcSeventhD`. -/
@[irreducible] def srcSeventhDRows : ℕ :=
    0x94100080100014880000c00094ba0000c000ad93c014c2a0b9b000ad7000142000140280 |||
    (0xe00000000000580000140000a80000ad0000b9800005000005c000 <<< 288)

/-- Packed composite mask data of the Seventh word. -/
def srcSeventhD : QMaskP := ⟨srcSeventhDCols, srcSeventhDRows, 14815734⟩

/-- Packed labels (17-bit fields) of `srcSeventhT`. -/
@[irreducible] def srcSeventhTLabs : ℕ :=
    0x42bc3e9e80b84059d1f3a015f52a76aa9c74c7b8dbd1bdaaeeb37c75960c7f8a3d251e7a |||
    (0x3e10b8aa5b754b8ac8646b9425b412f03acfd081ce40671aa714a77662c3d5da8cf49bb5 <<< 288) |||
    (0xaf7cbdfc513e36ecda02c0923399abc582d16a4c377ca0ae0cae84a46371f0b8f84a05ba <<< 576) |||
    (0x668da55e737578a0236e498eef9255c3b318d48ce63e471f210198c7c80b9d8543897252 <<< 864) |||
    (0x98d231049c9af7395d2531e94909e3ea71f510178c7d40ba6053ea970aaae8cc00452423 <<< 1152) |||
    (0x3ec1e36440a390f1306cb36159a0da2f566a2dd1b8163a75a62c50df7d7f7eb0536754f7 <<< 1440) |||
    (0xed1ca2e29848605cdcee6e726cee9b9c0998c6a4715fb4e950a29069488d540c79bcab13 <<< 1728) |||
    (0xd542c647232e425ac05d6024a3e358081f1303f5dba6485701fdebca5da3502e048785b4 <<< 2016) |||
    (0xa6729734e743a34faa1a3c5d1e24bf63478807c38f996055a946c68513c6f434b8ed1e7d <<< 2304) |||
    (0xe088386a2f43981e4ce8db868b0dc92ee492ab28b92424ea10dd0bffc870d3b4d47734f1 <<< 2592) |||
    (0x80811c29484c54b91b03bd49a2917443c9f033d875673aa3cb5f0eaaf00646fca3939e17 <<< 2880) |||
    (0x1bc7b694274a112ebbd2841a8eefb600eb3393f9e3ad0ef11db2bb7deabc755e129dbd57 <<< 3168) |||
    (0x452c5d9800f616a30d270950bc0fb1a00fa007c47f2216c4e4551cd33ebaddbb8d0eb0cb <<< 3456) |||
    (0x27afb517e9380a85e27d7d00804e9bef30e462b9377defdab9dc636d91f747f2e3f926ad <<< 3744) |||
    (0x139eaddd9075da7f4467b6ff1635722966ecc067b1b518e9388a85e67d9d3562295eecc0 <<< 4032) |||
    (0x3839d29b8108b80f6276d87bb284f38b688d2cd0fb715826e380fa6a040ce0ce600b0978 <<< 4320) |||
    (0x8f6c172e0a8f12e64560f97cf8a2fc6d99b41201138049c8111497bb059e009e27b74f81 <<< 4608) |||
    (0x471aabcccde2c89171fb28f614e5def11a470492fb5f37ab7ee62c2917ac7b6e3db2036e <<< 4896) |||
    (0x3f34bb9a20d9d99457d6c413b5ae950a097e7c816140a747da9027d4a62aab8af69ae3b1 <<< 5184) |||
    (0xe9bd46fa4d8ea1381f3f4053c02918fc100a0694a755603a8fdc7e68e7357ba9bd42cc36 <<< 5472) |||
    (0x1df1f7ec07bc03d18f7900f0695b954cf3a51dc59a904b58a69b5a2cf2cd4b8a4fbb3209 <<< 5760) |||
    (0x85bb42cacdbad0b0945f42efb27901ff0936443b227df4d6b4a5f3b2761edcd45024e92a <<< 6048) |||
    (0xa8336dd36a8c0bd1b9d00f4864abc0075c13aecef870022f81a0e70c507d39a4451a6df6 <<< 6336) |||
    (0x6fab0da51ce64b6c59c46a6102de60168b271356aed040d37a5fd46508fbd80f3a9b584d <<< 6624) |||
    (0xcf17dfa8fda5f8e8af1327f84cd8dd611d6ca2bbe1ea22dbb445d87365a70c31bb28ef14 <<< 6912) |||
    (0xc64d352b19d588f712c562bb82d1fe889f4e0c702342da3b22bb348e58e36a160428cb2f <<< 7200) |||
    (0x56d11a76d68b0c21d572e9b974c9d0a25d30282819f4246203b52fb194c35065c116d8ed <<< 7488) |||
    (0x2072ca889785bc8c91d16c619df68980b95ca9b054b8aa62153218238fb326a228c7e217 <<< 7776) |||
    (0x418d4a47111ea98f5580fc83b4a91576a160a41d1b0e3b26873d0b07cb9305c78a59a172 <<< 8064) |||
    (0x98f541abad4b6965a73d9a28ac89c5b43563ed900fac07e33a08bc9011a524d117c50ae4 <<< 8352) |||
    (0xc281b9d05de48c8d49268bbe29d722cc6c5238b9d04de4848d092689be28d7224c685238 <<< 8640) |||
    (0x9924f023508223728e006c0f1449f7b28504bde939b2008c087d927a35a08acdb04d9bf5 <<< 8928) |||
    (0x6fe3901090eeeff2f60238d0ddbb55168842ae328b <<< 9216)

/-- Packed numerators (8-bit fields, offset 128) of `srcSeventhT`. -/
@[irreducible] def srcSeventhTNums : ℕ :=
    0x7f817f817f81817f81817f81817d837d838383838383837d83837d7d7d7d837d837d7d7d |||
    (0x81817f817f7f7f7f817f7f7f7f817f7f7f7f7f7f81817f817f7f7f81818181817f7f817f <<< 288) |||
    (0x81817f7f817f818181818181817f81817f7f7f7f817f817f81817f817f7f7f7f7f7f8181 <<< 576) |||
    (0x7f7f7f7f7f817f7f7f8181817f7f7f7f7f7f8181817f7f81817f817f817f7f817f817f81 <<< 864) |||
    (0x7f7f817f7f817f817f81818181817f7f817f7f817f817f818181817f7f7f7f8181818181 <<< 1152) |||
    (0x7f7f8181817f7f817f817f7f81817f7f817f7f81817f7f7f7f7f81817f817f8181818181 <<< 1440) |||
    (0x7f81818181818181817f7f8181818181817f7f818181817f7f817f817f7f7f8181818181 <<< 1728) |||
    (0x837d838383837d7d837d7d8381817f7f817f7f8181817f8181817f817f817f81817f8181 <<< 2016) |||
    (0x8181817f7f81817f817f817f7f817f7f817f7f817f817f8181837d7d837d7d838383837d <<< 2304) |||
    (0x7f7f7f81818181818181818181817f8181817f7f7f817f7f817f818181817f7f81817f81 <<< 2592) |||
    (0x7f7f81817f81817f81817f8181817f7f81817f81817f7f7f7f817f817f7f7f7f8181817f <<< 2880) |||
    (0x7f7f817f81817f818181818181818181817f7f7f817f81817f7f7f7f81817f7f7f7f7f7f <<< 3168) |||
    (0x7f7f81817f81817f7f81817f817f817f7f817f7f817f7f81817f817f817f7f817f7f817f <<< 3456) |||
    (0x81817f7f81818181817f7f817f817f7f7f81817f7f81818181817f7f817f817f817f8181 <<< 3744) |||
    (0x818181817f7f8181817f817f8181817f81817f7f817f817f81817f7f817f817f7f818181 <<< 4032) |||
    (0x7f817f7f8181817f8181817f <<< 4320)

/-- The transported short list `srcSeventhT` (552 terms, source order). -/
def srcSeventhT : List (ℕ × ℤ) := srcDecodeTerms srcSeventhTLabs srcSeventhTNums 552

/-! ## Checks of the literal data -/

set_option maxRecDepth 100000 in
/-- The letter data of the Seventh word are certified. -/
theorem srcSeventhW_check : srcSeventhW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem srcSeventhD_ok : srcSeventhD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem srcSeventhD_cols : ∀ i : Fin 24, qmWordP (srcSeventhW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 srcSeventhD.colsP i.val, srcSeventhD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem srcSeventhD_rows : ∀ i : Fin 24,
    fld 24 srcSeventhD.rowsP i.val = rowsOf (fun j => fld 24 srcSeventhD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The Odd short block is transported onto the literal target list. -/
theorem srcSeventhT_check : shortCheckF srcSeventhD oddSrcShort.flat srcSeventhT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The target list has valid labels. -/
theorem srcSeventhT_labels : srcSeventhT.all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-! ## The local image -/

/-- The field-bound growth of the Seventh word (three Xi letters). -/
theorem srcSeventhH_growth : tensorWordGrowthAll srcSeventhH = 16777216 := by decide

/-- The tensor denominator of the Seventh word. -/
theorem srcSeventhH_den : tensorWordDenAll srcSeventhH = 4096 := by decide

/-- The packed tensor of `L · v_Odd` at width `w` (numerators over `4096`). -/
def srcSeventhYX (w : ℕ) : List SVec := tensorWordAll w srcSeventhH (oddSrcXW w)

/-- The identification vector of `L · v_Odd` at width `w`. -/
def srcSeventhY (w : ℕ) : IdentVec :=
  ⟨oddSrcMat.act identSpatialAlphabet srcSeventhH, ShortData.ofList srcSeventhT, 1 / 4,
    tensorRat w (srcSeventhYX w) ((tensorWordDenAll srcSeventhH : ℚ) * 1)⟩

/-- Bounds of the packed tensor of `L · v_Odd`. -/
theorem srcSeventhH_bound {w : ℕ} (hw : 28 ≤ w) : tensorWordGrowthAll srcSeventhH * 8 < 2 ^ w := by
  rw [srcSeventhH_growth]
  calc 16777216 * 8 < 2 ^ 28 := by norm_num
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw

/-- Bounds of the packed tensor of `L · v_Odd`. -/
theorem srcSeventhYX_bnd {w : ℕ} (hw : 28 ≤ w) : TBnd w (16777216 * 8) (srcSeventhYX w) := by
  have h := (tensorWordAll_actual srcSeventhH (oddSrcXW_bnd (w := w) (by omega))
    (srcSeventhH_bound hw) 1).1
  rw [srcSeventhH_growth] at h
  exact h

/-- The coordinates of `L · v_Odd`. -/
theorem srcSeventhY_actual {w : ℕ} (hw : 28 ≤ w) : griessConwayEncode (rhoLocal
    (identWordLocal srcSeventhH) (generatedAxisGlobalTwelveRepresentative 2)) =
      (srcSeventhY w).real :=
  IdentVec.word_actual (oddSrcVecW w) srcSeventhW srcSeventhW_check srcSeventhD srcSeventhD_ok
    srcSeventhD_cols srcSeventhD_rows srcSeventhT srcSeventhT_check _
    (tensorWordAll_actual srcSeventhH (oddSrcXW_bnd (w := w) (by omega))
      (srcSeventhH_bound hw) 1).2 _ (oddSrcW_rep (by omega))

/-- The Seventh word is the original local factor of the Seventh representative. -/
theorem srcSeventhH_local :
    identWordLocal srcSeventhH = localFiberIntoH generatedSeventhLocalFiber := by
  rw [identWordLocal]
  refine congrArg localFiberIntoH ?_
  change xiSpinLocalFiber * (generatedFourthMonomialFiberLetter (1, false) *
      (xiSpinLocalFiber * (generatedFourthMonomialFiberLetter (0, false) *
      (generatedFourthMonomialFiberLetter (1, false) *
      (generatedFourthMonomialFiberLetter (0, false) *
      (xiSpinLocalFiber * 1)))))) = generatedSeventhLocalFiber
  simp only [generatedFourthMonomialFiberLetter, Bool.false_eq_true, ↓reduceIte, mul_one,
    generatedSeventhLocalFiber, mul_assoc]

/-- The Seventh representative is the forward triality image of `L · v_Odd`. -/
theorem srcSeventh_rep_eq : generatedAxisGlobalTwelveRepresentative 6 =
    sExtra (rhoLocal (identWordLocal srcSeventhH)
      (generatedAxisGlobalTwelveRepresentative 2)) := by
  rw [srcSeventhH_local]
  rfl

/-- The short block of `L · v_Odd` satisfies the range conditions. -/
theorem srcSeventhY_ok (w : ℕ) : (srcSeventhY w).sh.ok = true :=
  ofList_ok srcSeventhT srcSeventhT_labels

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
