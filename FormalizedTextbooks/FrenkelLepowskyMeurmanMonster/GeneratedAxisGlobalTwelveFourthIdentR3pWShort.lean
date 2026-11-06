/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentDataR3p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentDataR3pW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSlices
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfth

/-! # Chunked target short transport checks of the Fourth identification `R3p`

Each slice of the literal Twelfth source short list `twelfthLitShort.flat` (workers gtwelfth,
r8f) is transported by the composite data of the target word onto the corresponding chunk of the
target short list; one kernel evaluation per slice. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Slice 0 of the target short transport. -/
theorem fourthR3p_wchunk0 :
    shortCheckF fourthR3pGD ((slices twelfthLitShort.flat [4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096]).getD 0 [])
      (fourthR3pGTChunks.getD 0 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Slice 1 of the target short transport. -/
theorem fourthR3p_wchunk1 :
    shortCheckF fourthR3pGD ((slices twelfthLitShort.flat [4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096]).getD 1 [])
      (fourthR3pGTChunks.getD 1 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Slice 2 of the target short transport. -/
theorem fourthR3p_wchunk2 :
    shortCheckF fourthR3pGD ((slices twelfthLitShort.flat [4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096]).getD 2 [])
      (fourthR3pGTChunks.getD 2 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Slice 3 of the target short transport. -/
theorem fourthR3p_wchunk3 :
    shortCheckF fourthR3pGD ((slices twelfthLitShort.flat [4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096]).getD 3 [])
      (fourthR3pGTChunks.getD 3 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Slice 4 of the target short transport. -/
theorem fourthR3p_wchunk4 :
    shortCheckF fourthR3pGD ((slices twelfthLitShort.flat [4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096]).getD 4 [])
      (fourthR3pGTChunks.getD 4 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Slice 5 of the target short transport. -/
theorem fourthR3p_wchunk5 :
    shortCheckF fourthR3pGD ((slices twelfthLitShort.flat [4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096]).getD 5 [])
      (fourthR3pGTChunks.getD 5 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Slice 6 of the target short transport. -/
theorem fourthR3p_wchunk6 :
    shortCheckF fourthR3pGD ((slices twelfthLitShort.flat [4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096]).getD 6 [])
      (fourthR3pGTChunks.getD 6 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Slice 7 of the target short transport. -/
theorem fourthR3p_wchunk7 :
    shortCheckF fourthR3pGD ((slices twelfthLitShort.flat [4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096]).getD 7 [])
      (fourthR3pGTChunks.getD 7 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Slice 8 of the target short transport. -/
theorem fourthR3p_wchunk8 :
    shortCheckF fourthR3pGD ((slices twelfthLitShort.flat [4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096]).getD 8 [])
      (fourthR3pGTChunks.getD 8 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Slice 9 of the target short transport. -/
theorem fourthR3p_wchunk9 :
    shortCheckF fourthR3pGD ((slices twelfthLitShort.flat [4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096]).getD 9 [])
      (fourthR3pGTChunks.getD 9 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Slice 10 of the target short transport. -/
theorem fourthR3p_wchunk10 :
    shortCheckF fourthR3pGD ((slices twelfthLitShort.flat [4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096]).getD 10 [])
      (fourthR3pGTChunks.getD 10 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Slice 11 of the target short transport. -/
theorem fourthR3p_wchunk11 :
    shortCheckF fourthR3pGD ((slices twelfthLitShort.flat [4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096]).getD 11 [])
      (fourthR3pGTChunks.getD 11 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The slices of the source list and the target chunks have equal lengths. -/
theorem fourthR3p_wlens : ∀ i < 12,
    ((slices twelfthLitShort.flat [4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096]).getD i []).length = (fourthR3pGTChunks.getD i []).length := by
  decide +kernel

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
