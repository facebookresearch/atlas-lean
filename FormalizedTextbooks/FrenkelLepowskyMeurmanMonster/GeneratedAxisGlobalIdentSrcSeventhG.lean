/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhF

/-! # The Seventh source vector with literal short block and tensor columns of any width

`seventhSrcVecG w` has the literal short block of `seventhSrcVecF` and the packed tensor block of
`seventhSrcVecW w`.  Both `seventhSrcVecF` and `seventhSrcVecW w` represent family representative
`6`, so their short blocks agree as real vectors and `seventhSrcVecG w` represents it too: wide
tensor columns are available without re-evaluating the short block. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of the Seventh source with columns of width `w`. -/
def srcSeventhX0W (w : ℕ) : List SVec := twTriTen w 2048 (srcSeventhYX w) (srcSeventhYL w).sh.odd

/-- The Seventh source vector with the literal short block and tensor columns of width `w`. -/
def seventhSrcVecG (w : ℕ) : IdentVec :=
  ⟨srcSeventhMat, srcSeventhShF, 1 / srcSeventhD0, tensorRat w (srcSeventhX0W w) srcSeventhD0⟩

/-- The representation of family representative `6` with the literal short block and tensor
columns of width `w`. -/
theorem seventhSrcG_rep {w : ℕ} (hw : 31 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 6) = (seventhSrcVecG w).real := by
  have hW := seventhSrcW_rep hw
  have hF := seventhSrcF_rep
  have hs : (seventhSrcVecW w).real.2.1 = seventhSrcVecF.real.2.1 := by rw [← hW, ← hF]
  rw [hW]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [IdentVec.real_fst, IdentVec.real_fst]
    rfl
  · rw [hs, IdentVec.real_short, IdentVec.real_short]
    rfl
  · rw [IdentVec.real_tensor, IdentVec.real_tensor]
    rfl

/-- The short block of `seventhSrcVecG w` satisfies the range conditions. -/
theorem seventhSrcVecG_ok (w : ℕ) : (seventhSrcVecG w).sh.ok = true := seventhSrcVecF_ok

/-- Bounds of the packed tensor of `seventhSrcVecG w`. -/
theorem srcSeventhX0W_bnd {w : ℕ} (hw : 31 ≤ w) :
    TBnd w (4 * (16777216 * 8) + 276 * 6144) (srcSeventhX0W w) :=
  seventhSrcVecW_bnd hw

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
