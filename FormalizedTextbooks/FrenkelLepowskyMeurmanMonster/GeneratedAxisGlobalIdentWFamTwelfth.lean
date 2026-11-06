/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentFlatSource

/-! # Factory glue for the Twelfth source (r8f)

The identification factory needs, per family, a source vector with a literal short block, a
packed tensor block with a numeric bound, the representation lemma for every large width, and the
matrix block as an integer block.  For the Twelfth family (representative `10`) these come from
gtwelfth's literal-short vector `twelfthSrcVecL` (`twelfthSrcL_rep`): `twelfthSrcVecT w` is the
same vector with its short scale written as the literal `1 / 128`, its short block is
`twelfthLitShort` (the literal flat list `twelfthFlatLit`, decoded by halving), its tensor block
is the re-spaced compact literal `twelfthSrcXW w` over `32` (bound `15`, `twelfthSrcXW_bnd`), and
`twelfthSrcMatZ` is the matrix block with coefficients over `16`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false

/-- The literal short block of the Twelfth source. -/
def twelfthLitShort : ShortData := ShortData.ofList twelfthFlatLit

/-- The packed tensor block of the Twelfth source at width `w`. -/
def twelfthSrcXW (w : ℕ) : List SVec := twWidenT 4 w twelfthX12Lit

/-- The factory-ready Twelfth source vector (literal short block, scale `1 / 128`). -/
def twelfthSrcVecT (w : ℕ) : IdentVec :=
  ⟨twelfthSrcMat, twelfthLitShort, 1 / 128, tensorRat w (twelfthSrcXW w) 32⟩

/-- The factory-ready Twelfth source vector represents family representative `10`. -/
theorem twelfthSrcT_rep {w : ℕ} (hw : 4 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 10) =
      (twelfthSrcVecT w).real := by
  rw [twelfthSrcL_rep w hw]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [IdentVec.real_fst, IdentVec.real_fst]
    rfl
  · rw [IdentVec.real_short, IdentVec.real_short, twelfthSrcVecL_sden]
    rfl
  · rw [IdentVec.real_tensor, IdentVec.real_tensor]
    rfl

/-- The tensor bound of the Twelfth source. -/
theorem twelfthSrcXW_bnd {w : ℕ} (hw : 4 ≤ w) : TBnd w 15 (twelfthSrcXW w) :=
  twelfthSrcXC_bnd w hw

/-- The vector `e_i + e_j` (the unit vector `e_i` for `i = j`) as an integer list. -/
def twelfthUnitSumZ (i j : ℕ) : List ℤ :=
  (List.range 24).map (fun t => if t = i ∨ t = j then 1 else 0)

/-- The Twelfth source block as an integer block (coefficients over `16`). -/
def twelfthSrcMatZ : MatZ :=
  ⟨5 / 16, 16, [
    (1, twelfthUnitSumZ 0 2), (-1, twelfthUnitSumZ 0 3), (1, twelfthUnitSumZ 0 18),
    (-1, twelfthUnitSumZ 0 19), (1, twelfthUnitSumZ 1 2), (1, twelfthUnitSumZ 1 3),
    (1, twelfthUnitSumZ 1 18), (1, twelfthUnitSumZ 1 19), (-1, twelfthUnitSumZ 2 16),
    (1, twelfthUnitSumZ 2 17), (1, twelfthUnitSumZ 3 16), (1, twelfthUnitSumZ 3 17),
    (1, twelfthUnitSumZ 16 18), (-1, twelfthUnitSumZ 16 19), (-1, twelfthUnitSumZ 17 18),
    (-1, twelfthUnitSumZ 17 19), (-4, twelfthUnitSumZ 1 1), (4, twelfthUnitSumZ 19 19)], 0⟩

set_option maxRecDepth 100000 in
/-- The rank-one terms of the Twelfth source block are those of its integer block. -/
theorem twelfthSrcMat_terms_eqZ : twelfthSrcMat.terms = twelfthSrcMatZ.toRep.terms := by
  decide +kernel

/-- The Twelfth source block is the rational block of its integer block. -/
theorem twelfthSrcMat_eqZ : twelfthSrcMat = twelfthSrcMatZ.toRep := by
  have h := twelfthSrcMat_terms_eqZ
  unfold twelfthSrcMat MatZ.toRep at h ⊢
  exact congrArg₂ MatRep.mk (by rfl) h

/-- Entries of a transported Twelfth source block from integer data. -/
theorem twelfthSrcMat_act_entryZ (w : List IdentLetter) (i j : Fin 24) :
    (twelfthSrcMat.act identSpatialAlphabet w).entry i j =
      (twelfthSrcMatZ.act w).entry i j := by
  rw [twelfthSrcMat_eqZ, MatZ.act_entry]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
