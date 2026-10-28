/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # The Seventh source vector with fast tensor columns

The packed tensor of the Seventh source word image is recomputed with the fast Xi letter
(`tensorPlanF`, one plan step per letter), which has the same rational tensor
(`tensorPlanF_rat`).  The triality image `seventhSrcVecWF w` of the resulting word image vector
represents family representative `6` (`twTriVec_actual`, with the checks of
`GeneratedAxisGlobalIdentSrcSeventh` transferred along the unchanged matrix and short blocks), and
`seventhSrcVecGF w` combines its tensor block with the literal short block of `seventhSrcVecF`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- A plan with one step per letter expands to the word. -/
theorem planWord_letters : ∀ ls : List IdentLetter, planWord (ls.map TPlan.letter) = ls
  | [] => rfl
  | l :: ls => by
    change TPlan.word (TPlan.letter l) ++ planWord (ls.map TPlan.letter) = l :: ls
    rw [planWord_letters ls]
    rfl

/-- A plan with one step per letter is admissible. -/
theorem planOk_letters : ∀ ls : List IdentLetter, planOk (ls.map TPlan.letter) = true
  | [] => rfl
  | l :: ls => by
    change ((TPlan.letter l).ok && planOk (ls.map TPlan.letter)) = true
    rw [planOk_letters ls]
    rfl

/-- The tensor plan of the Seventh source word. -/
def srcSeventhHP : List TPlan := srcSeventhH.map TPlan.letter

/-- The plan expands to the Seventh source word. -/
theorem srcSeventhHP_word : planWord srcSeventhHP = srcSeventhH := planWord_letters _

/-- The plan of the Seventh source word is admissible. -/
theorem srcSeventhHP_ok : planOk srcSeventhHP = true := planOk_letters _

/-- The packed tensor of the Seventh word image of the Odd axis, with the fast Xi letter. -/
def srcSeventhYXF (w : ℕ) : List SVec := tensorPlanF w srcSeventhHP (oddSrcXW w)

/-- Bounds of the fast packed tensor of the Seventh word image. -/
theorem srcSeventhYXF_bnd {w : ℕ} (hw : 28 ≤ w) : TBnd w (16777216 * 8) (srcSeventhYXF w) := by
  have h := (tensorPlanF_actual srcSeventhHP srcSeventhHP_ok (oddSrcXW_bnd (w := w) (by omega))
    (by rw [srcSeventhHP_word]; exact srcSeventhH_bound hw) 1).1
  rw [srcSeventhHP_word, srcSeventhH_growth] at h
  exact h

/-- The fast packed tensor has the rational tensor of the packed word tensor. -/
theorem srcSeventhYXF_rat {w : ℕ} (hw : 28 ≤ w) :
    tensorRat w (srcSeventhYXF w) ((tensorWordDenAll srcSeventhH : ℚ) * 1) =
      tensorRat w (srcSeventhYX w) ((tensorWordDenAll srcSeventhH : ℚ) * 1) := by
  have h := tensorPlanF_rat srcSeventhHP srcSeventhHP_ok (oddSrcXW_bnd (w := w) (by omega))
    (by rw [srcSeventhHP_word]; exact srcSeventhH_bound hw) 1
  rw [srcSeventhHP_word] at h
  exact h

/-- The Seventh word image of the Odd axis with the fast packed tensor. -/
def srcSeventhYLF (w : ℕ) : IdentVec :=
  ⟨srcSeventhYMat, srcSeventhYSh, 1 / 4,
    tensorRat w (srcSeventhYXF w) ((tensorWordDenAll srcSeventhH : ℚ) * 1)⟩

/-- The fast word image vector is the literal word image vector. -/
theorem srcSeventhYLF_eq {w : ℕ} (hw : 28 ≤ w) : srcSeventhYLF w = srcSeventhYL w := by
  unfold srcSeventhYLF srcSeventhYL
  rw [srcSeventhYXF_rat hw]

/-- The Seventh axis as the triality image of the fast word image vector. -/
def seventhSrcVecWF (w : ℕ) : IdentVec :=
  twTriVec w (srcSeventhYLF w) (srcSeventhYXF w) ((tensorWordDenAll srcSeventhH : ℚ) * 1)
    srcSeventhMat srcSeventhP srcSeventhOs 256 2048

/-- The Seventh representative has the coordinates of `seventhSrcVecWF w`. -/
theorem seventhSrcWF_rep {w : ℕ} (hw : 31 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 6) = (seventhSrcVecWF w).real := by
  have hlen : (srcSeventhYLF w).sh.odd.length = 276 := srcSeventh_odd_length w
  rw [srcSeventh_rep_eq]
  apply twTriVec_actual w (16777216 * 8) 6144 (srcSeventhYLF w) (srcSeventhYXF w) _ srcSeventhMat
    srcSeventhP srcSeventhOs 256 2048
    (by rw [srcSeventhYLF_eq (by omega), srcSeventhYL_eq]; exact srcSeventhY_ok w) rfl
    (by rw [srcSeventhH_den]; norm_num) (srcSeventhYXF_bnd (by omega)) (srcSeventh_odd_bound w)
  · rw [hlen]
    calc 4 * (16777216 * 8) + 276 * 6144 < 2 ^ 31 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  · change ((2048 : ℤ) : ℚ) = 1 / 4 * (2 * ((tensorWordDenAll srcSeventhH : ℚ) * 1))
    rw [srcSeventhH_den]
    norm_num
  · change ((256 : ℤ) : ℚ) / (2 * ((tensorWordDenAll srcSeventhH : ℚ) * 1)) = 1 / 4 / 8
    rw [srcSeventhH_den]
    norm_num
  · rw [srcTwMatCheck_congr _ (srcSeventhYLF w) (srcSeventhYL w) rfl rfl rfl]
    exact srcSeventhMat_check w
  · rw [srcTwPairCheck_congr _ (srcSeventhYLF w) (srcSeventhYL w) _ rfl rfl rfl]
    exact srcSeventhP_check w
  · rw [srcTwOctCheck_congr _ (srcSeventhYLF w) (srcSeventhYL w) rfl]
    exact srcSeventhOs_check w
  · rw [srcSeventhYLF_eq (by omega), srcSeventhYL_eq]
    exact srcSeventhY_actual (by omega)

/-- The fast packed tensor of the Seventh source. -/
def srcSeventhX0F (w : ℕ) : List SVec := twTriTen w 2048 (srcSeventhYXF w) (srcSeventhYL w).sh.odd

/-- Bounds of the fast packed tensor of the Seventh source. -/
theorem srcSeventhX0F_bnd {w : ℕ} (hw : 31 ≤ w) :
    TBnd w (4 * (16777216 * 8) + 276 * 6144) (srcSeventhX0F w) := by
  have h := twTriTen_bnd w (16777216 * 8) 6144 2048 (srcSeventhYXF w) (srcSeventhYL w).sh.odd
    (srcSeventhYXF_bnd (by omega)) (by simpa [List.all_eq_true] using srcSeventh_odd_bound w)
    (by rw [srcSeventh_odd_length]
        calc 4 * (16777216 * 8) + 276 * 6144 < 2 ^ 31 := by norm_num
          _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw)
  rw [srcSeventh_odd_length] at h
  exact h

/-- The Seventh source vector with the literal short block and the fast packed tensor. -/
def seventhSrcVecGF (w : ℕ) : IdentVec :=
  ⟨srcSeventhMat, srcSeventhShF, 1 / srcSeventhD0, tensorRat w (srcSeventhX0F w) srcSeventhD0⟩

/-- The representation of family representative `6` with the literal short block and the fast
packed tensor of width `w`. -/
theorem seventhSrcGF_rep {w : ℕ} (hw : 31 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 6) = (seventhSrcVecGF w).real := by
  have hW := seventhSrcWF_rep hw
  have hF := seventhSrcF_rep
  have hs : (seventhSrcVecWF w).real.2.1 = seventhSrcVecF.real.2.1 := by rw [← hW, ← hF]
  rw [hW]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [IdentVec.real_fst, IdentVec.real_fst]
    rfl
  · rw [hs, IdentVec.real_short, IdentVec.real_short]
    rfl
  · rw [IdentVec.real_tensor, IdentVec.real_tensor]
    rfl

/-- The short block of `seventhSrcVecGF w` satisfies the range conditions. -/
theorem seventhSrcVecGF_ok (w : ℕ) : (seventhSrcVecGF w).sh.ok = true := seventhSrcVecF_ok

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
