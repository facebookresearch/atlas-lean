/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfth
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWTwelfthLitOct
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWTwelfthLitOdd

/-! # Kernel-cheap factory glue for the Twelfth source (r8f)

The short block `twelfthLitShort = ShortData.ofList twelfthFlatLit` of `twelfthSrcVecT` is costly in
the kernel for the 46760-term transport checks of the factory: decoding by halving builds the list
through about a million appends, and `ShortData.ofList` adds three filter passes.  `twelfthShS` is
the same flat list (`twelfthShS_flat`) as a structured short block whose parts decode linearly from
small packed numbers: the pair terms `twelfthSrcPairs128`, the octad blocks `twelfthLitOct` and the
odd terms `twelfthLitOddCol j` column by column.  `twelfthSrcVecS w` is the factory-ready Twelfth
source with this short block (`twelfthSrcS_rep`); its tensor block, tensor bound and integer matrix
glue are those of `twelfthSrcVecT`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false

/-- The structured short block of the Twelfth source (pairs, octad blocks, odd columns). -/
def twelfthShS : ShortData :=
  ⟨twelfthSrcPairs128, twelfthLitOct, (List.range 24).flatMap twelfthLitOddCol⟩

/-- The flat terms of the structured short block are gtwelfth's literal flat list. -/
theorem twelfthShS_flat : twelfthShS.flat = twelfthFlatLit := by
  change twelfthSrcPairs128 ++ octsFlat twelfthLitOct ++
      (List.range 24).flatMap twelfthLitOddCol =
    twelfthSrcPairs128 ++ twelfthOctLit ++ (List.range 24).flatMap twelfthOddLit
  rw [twelfthLitOct_flat, twelfthLitOdd_flat]

/-- The factory-ready Twelfth source vector (structured short block, scale `1 / 128`). -/
def twelfthSrcVecS (w : ℕ) : IdentVec :=
  ⟨twelfthSrcMat, twelfthShS, 1 / 128, tensorRat w (twelfthSrcXW w) 32⟩

/-- The factory-ready Twelfth source vector represents family representative `10`. -/
theorem twelfthSrcS_rep {w : ℕ} (hw : 4 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 10) =
      (twelfthSrcVecS w).real := by
  have h : shortVec twelfthLitShort.flat = shortVec twelfthShS.flat := by
    rw [twelfthShS_flat]
    exact shortVec_ofList twelfthFlatLit
  rw [twelfthSrcT_rep hw]
  exact IdentVec.real_short_congr twelfthSrcMat twelfthLitShort twelfthShS (1 / 128)
    (tensorRat w (twelfthSrcXW w) 32) h

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
