/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpatialRational

/-! Candidate exact original spatial directions, checked against full source products separately. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Candidate rational coordinate vectors for all nine original odd-family root products. -/
def generatedAxisGlobalOddSpatialRootVectorQ : Fin 9 → Fin 24 → ℚ :=
  ![![0, 0, 0, 0, -1/4, 0, -1/4, 0,
      -1/4, 1/4, 0, 0, 0, -1/4, -1/4, 0,
      0, 1/4, 0, 3/4, 0, 0, 0, 0],
    ![-1/2, 0, 0, 0, 1/4, -1/4, -1/4, -1/4,
      0, -1/4, 1/4, 0, 0, -1/4, 1/4, 0,
      0, 1/4, -1/4, 0, -1/4, 0, 0, 1/4],
    ![-1/2, 1/2, 1/4, 1/4, 0, 0, -1/4, -1/4,
      1/4, -1/4, 0, 0, 1/4, -1/4, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0],
    ![-1/4, 0, 0, 1/4, 1/4, 0, -1/4, 0,
      1/4, -1/4, 0, 0, 1/4, -1/4, -1/4, -1/4,
      1/4, -1/4, -1/4, -1/4, -1/4, 1/4, 0, 0],
    ![1/4, 1/4, 1/4, -1/4, -1/4, -1/4, -1/4, 1/4,
      1/4, 1/4, 1/4, -1/4, -1/4, -1/4, -1/4, 1/4,
      0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1/2, 0, 0, 1/2, 0, 1/2, 1/2, 0],
    ![1/8, 1/8, 1/8, 3/8, 1/8, 1/8, 1/8, 3/8,
      1/8, -1/8, -1/8, -1/8, -1/8, 1/8, 1/8, -3/8,
      3/8, -1/8, -1/8, 1/8, 3/8, -1/8, -1/8, 1/8],
    ![1/8, 1/8, -1/8, -1/8, -1/8, -1/8, 1/8, 1/8,
      -1/8, 1/8, -3/8, -5/8, -1/8, 1/8, 1/8, -1/8,
      -1/8, 1/8, 3/8, 1/8, 1/8, -1/8, 1/8, -1/8]]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
