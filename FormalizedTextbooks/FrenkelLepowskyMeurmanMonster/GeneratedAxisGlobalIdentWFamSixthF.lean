/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSX6

/-! # Factory glue for the Sixth source with the compact tensor (gident2)

The kernel evaluation of `sixthSrcXW w` (a sum of `4096` single entries per column) exceeds the
memory budget of an identification part.  grecip's compact tensor `sixthSXF w` (8-bit columns
respaced to width `w`) has the same rational tensor (`sixthSXF_ten`) and the field bound
`2 ^ 8 - 1`; `sixthSrcVecF w` is the factory-ready Sixth source vector with this tensor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false

/-- The factory-ready Sixth source vector (literal short block, compact tensor). -/
def sixthSrcVecF (w : ℕ) : IdentVec :=
  ⟨sixthSrcMat, sixthLitShort, 1 / 32, tensorRat w (sixthSXF w) 32⟩

/-- The factory-ready Sixth source vector represents family representative `5`. -/
theorem sixthSrcF_rep {w : ℕ} (hw : 19 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 5) = (sixthSrcVecF w).real := by
  rw [sixthSrcL_rep hw]
  unfold sixthSrcVecL sixthSrcVecF
  rw [sixthSXF_ten hw]

/-- The field bound of the compact Sixth tensor. -/
theorem sixthSXF_bndF {w : ℕ} (hw : 19 ≤ w) : TBnd w (2 ^ 8 - 1) (sixthSXF w) :=
  sixthSXF_bnd (by omega)

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
