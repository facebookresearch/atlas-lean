/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite candidate-coordinate matching and actual projective source-path separation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3SortedPaths
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3ProjectiveCodes
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorChecked

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- All 1080 finite coordinate codes are reduced against the literal original path coordinates.
/-- Every listed code is the actual code of its checked finite path-vector coordinates. -/
theorem y422Orthogonal3SortedCode_cache (i : Fin 1080) :
    y422Orthogonal3ProjectiveVectorCode
      (y422Orthogonal3VectorCache (y422Orthogonal3SortedPath i)) =
      y422Orthogonal3SortedCode i := by
  revert i
  decide +kernel

/-- Every listed projective code is the code of the actual original source-word action. -/
theorem y422Orthogonal3SortedCode_actual (i : Fin 1080) :
    y422Orthogonal3ProjectiveVectorCode
      (y422Orthogonal3TPathVector (y422Orthogonal3SortedPath i)) =
      y422Orthogonal3SortedCode i := by
  rw [y422Orthogonal3VectorCache_actual, y422Orthogonal3SortedCode_cache]

/-- These 1080 actual original source-path images have pairwise distinct projective vector codes. -/
theorem y422Orthogonal3SortedPath_projectiveCode_injective :
    Function.Injective (fun i : Fin 1080 => y422Orthogonal3ProjectiveVectorCode
      (y422Orthogonal3TPathVector (y422Orthogonal3SortedPath i))) := by
  intro i j h
  apply y422Orthogonal3SortedCode_strictMono.injective
  simpa only [y422Orthogonal3SortedCode_actual] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
