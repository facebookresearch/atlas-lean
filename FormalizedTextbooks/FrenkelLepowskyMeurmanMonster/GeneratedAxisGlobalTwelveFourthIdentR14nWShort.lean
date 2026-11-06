/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentDataR14n
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentDataR14nW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSrcLit6

/-! # Chunked target short transport checks of the Fourth identification `R14n`

Each chunk of the literal Sixth source short list is transported by the composite data of the
target word onto the corresponding chunk of the target short list; one kernel evaluation per
chunk. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Chunk 0 of the target short transport. -/
theorem fourthR14n_wchunk0 :
    shortCheckF fourthR14nGD (fourthSrcLit6Chunks.getD 0 [])
      (fourthR14nGTChunks.getD 0 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Chunk 1 of the target short transport. -/
theorem fourthR14n_wchunk1 :
    shortCheckF fourthR14nGD (fourthSrcLit6Chunks.getD 1 [])
      (fourthR14nGTChunks.getD 1 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Chunk 2 of the target short transport. -/
theorem fourthR14n_wchunk2 :
    shortCheckF fourthR14nGD (fourthSrcLit6Chunks.getD 2 [])
      (fourthR14nGTChunks.getD 2 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Chunk 3 of the target short transport. -/
theorem fourthR14n_wchunk3 :
    shortCheckF fourthR14nGD (fourthSrcLit6Chunks.getD 3 [])
      (fourthR14nGTChunks.getD 3 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Chunk 4 of the target short transport. -/
theorem fourthR14n_wchunk4 :
    shortCheckF fourthR14nGD (fourthSrcLit6Chunks.getD 4 [])
      (fourthR14nGTChunks.getD 4 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Chunk 5 of the target short transport. -/
theorem fourthR14n_wchunk5 :
    shortCheckF fourthR14nGD (fourthSrcLit6Chunks.getD 5 [])
      (fourthR14nGTChunks.getD 5 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Chunk 6 of the target short transport. -/
theorem fourthR14n_wchunk6 :
    shortCheckF fourthR14nGD (fourthSrcLit6Chunks.getD 6 [])
      (fourthR14nGTChunks.getD 6 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Chunk 7 of the target short transport. -/
theorem fourthR14n_wchunk7 :
    shortCheckF fourthR14nGD (fourthSrcLit6Chunks.getD 7 [])
      (fourthR14nGTChunks.getD 7 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Chunk 8 of the target short transport. -/
theorem fourthR14n_wchunk8 :
    shortCheckF fourthR14nGD (fourthSrcLit6Chunks.getD 8 [])
      (fourthR14nGTChunks.getD 8 []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The chunks of the source and target lists have equal lengths. -/
theorem fourthR14n_wlens : ∀ i < fourthSrcLit6Chunks.length,
    (fourthSrcLit6Chunks.getD i []).length = (fourthR14nGTChunks.getD i []).length := by
  decide +kernel

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
