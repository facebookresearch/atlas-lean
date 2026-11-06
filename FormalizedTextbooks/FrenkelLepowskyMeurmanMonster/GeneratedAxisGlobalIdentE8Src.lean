/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcOdd
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcTen

/-! # Materialized Eighth source: the identification vector with literal blocks

`e8SrcVec` is `eighthSrcVecW 64` (worker `gforest`) with every computed block replaced by the
literals of `GeneratedAxisGlobalIdentE8SrcData`, each checked against the defining computation in
its own kernel check; `e8Src_rep` binds it to the Eighth representative.  The tensor carries the
tight bound `10496` (`e8SrcTen_tight`) instead of the coarse `2^29`, so words on it fit in field
width `64`.  Reused by every identification with Eighth source or target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The Eighth source with literal blocks. -/
def e8SrcVec : IdentVec :=
  ⟨srcEighthMat, ⟨srcEighthP, e8SrcOctLit, (List.range 24).flatMap e8OddColLit⟩,
    1 / (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)),
    tensorRat 64 e8SrcTenLit (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))⟩

/-- The literal source is the computed source. -/
theorem e8SrcVec_eq : e8SrcVec = eighthSrcVecW 64 := by
  unfold eighthSrcVecW twTriVec
  rw [e8YLit_eq, e8SrcOddCols_eq, e8SrcOct_eq, e8SrcTen_eq]
  rfl

/-- The literal source gives the genuine coordinates of the Eighth representative. -/
theorem e8Src_rep : griessConwayEncode (generatedAxisGlobalTwelveRepresentative 7) = e8SrcVec.real := by
  rw [e8SrcVec_eq]
  exact eighthSrcW_rep (by norm_num)

/-- The short block of the literal source satisfies the range conditions. -/
theorem e8SrcVec_ok : e8SrcVec.sh.ok = true := by
  rw [e8SrcVec_eq]
  exact eighthSrcVecW_ok 64

/-- The tensor block of the literal source. -/
theorem e8SrcVec_ten : e8SrcVec.ten =
    tensorRat 64 e8SrcTenLit (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)) := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
