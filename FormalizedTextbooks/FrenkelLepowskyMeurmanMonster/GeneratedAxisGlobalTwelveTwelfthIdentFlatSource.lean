/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentFlatOctB
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentFlatOdd0
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentFlatOdd1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentRegroupI

/-! # The Twelfth axis as an identification vector with literal short data

`twelfthSrcVecL w` is `twelfthSrcVecC w` with its short block replaced by the literal flat list
`twelfthFlatLit` (the pair terms, the octad table and the odd tables), which the kernel decodes
cheaply; the computed and the literal lists agree (`twelfthFlat_eq`, from the checks of the octad
and odd modules). `twelfthSrcL_rep` binds it to the genuine coordinates of the Twelfth axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The computed odd terms are the literal odd tables. -/
theorem twelfthOdd_eq : twTriOdd 24 twelfthYXC = (List.range 24).flatMap twelfthOddLit := by
  apply List.flatMap_congr
  intro j hj
  have hj' : j < 24 := List.mem_range.mp hj
  interval_cases j
  · exact twLBEq_eq _ _ twelfthOdd_check0
  · exact twLBEq_eq _ _ twelfthOdd_check1
  · exact twLBEq_eq _ _ twelfthOdd_check2
  · exact twLBEq_eq _ _ twelfthOdd_check3
  · exact twLBEq_eq _ _ twelfthOdd_check4
  · exact twLBEq_eq _ _ twelfthOdd_check5
  · exact twLBEq_eq _ _ twelfthOdd_check6
  · exact twLBEq_eq _ _ twelfthOdd_check7
  · exact twLBEq_eq _ _ twelfthOdd_check8
  · exact twLBEq_eq _ _ twelfthOdd_check9
  · exact twLBEq_eq _ _ twelfthOdd_check10
  · exact twLBEq_eq _ _ twelfthOdd_check11
  · exact twLBEq_eq _ _ twelfthOdd_check12
  · exact twLBEq_eq _ _ twelfthOdd_check13
  · exact twLBEq_eq _ _ twelfthOdd_check14
  · exact twLBEq_eq _ _ twelfthOdd_check15
  · exact twLBEq_eq _ _ twelfthOdd_check16
  · exact twLBEq_eq _ _ twelfthOdd_check17
  · exact twLBEq_eq _ _ twelfthOdd_check18
  · exact twLBEq_eq _ _ twelfthOdd_check19
  · exact twLBEq_eq _ _ twelfthOdd_check20
  · exact twLBEq_eq _ _ twelfthOdd_check21
  · exact twLBEq_eq _ _ twelfthOdd_check22
  · exact twLBEq_eq _ _ twelfthOdd_check23

/-- The literal flat short list of the Twelfth axis. -/
def twelfthFlatLit : List (ℕ × ℤ) :=
  twelfthSrcPairs128 ++ twelfthOctLit ++ (List.range 24).flatMap twelfthOddLit

/-- The computed flat short list is the literal list. -/
theorem twelfthFlat_eq : twelfthSrcVecC0.sh.flat = twelfthFlatLit := by
  change twelfthSrcPairs128 ++ octsFlat (twTriOct 1 twelfthYC.sh.oct twelfthSrcOcts) ++
    twTriOdd 24 twelfthYXC = _
  rw [twelfthOct_eq, twelfthOdd_eq]
  rfl

/-- The Twelfth axis with literal short data and the compact tensor block. -/
def twelfthSrcVecL (w : ℕ) : IdentVec :=
  ⟨twelfthSrcMat, ShortData.ofList twelfthFlatLit, (twelfthSrcVecC w).sden,
    tensorRat w (twWidenT 4 w twelfthX12Lit) 32⟩

/-- The literal representation has the coordinates of the compact one. -/
theorem twelfthSrcVecL_real (w : ℕ) : (twelfthSrcVecL w).real = (twelfthSrcVecC w).real := by
  have h := IdentVec.real_short_congr twelfthSrcMat (ShortData.ofList twelfthFlatLit)
    twelfthSrcVecC0.sh (twelfthSrcVecC w).sden (tensorRat w (twWidenT 4 w twelfthX12Lit) 32)
    (by rw [shortVec_ofList, twelfthFlat_eq])
  exact h

/-- The representation of family representative `10` with literal short data. -/
theorem twelfthSrcL_rep (w : ℕ) (hw : 4 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 10) = (twelfthSrcVecL w).real := by
  rw [twelfthSrcVecL_real]
  exact twelfthSrcC_rep w hw

set_option maxRecDepth 100000 in
/-- The literal flat list has valid labels. -/
theorem twelfthFlat_labels : twelfthFlatLit.all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The short block of the literal representation satisfies the range conditions. -/
theorem twelfthSrcVecL_ok (w : ℕ) : (twelfthSrcVecL w).sh.ok = true :=
  ofList_ok _ twelfthFlat_labels

/-- The tensor block of the literal representation. -/
theorem twelfthSrcVecL_ten (w : ℕ) :
    (twelfthSrcVecL w).ten = tensorRat w (twWidenT 4 w twelfthX12Lit) 32 := rfl

/-- The short scale of the literal representation. -/
theorem twelfthSrcVecL_sden (w : ℕ) : (twelfthSrcVecL w).sden = 1 / 128 := twelfthSrcVecC_sden w

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
