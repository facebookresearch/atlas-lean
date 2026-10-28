/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairCoordinates

/-! Executable inverse of the genuine original finite preferred coordinate-pair catalogue. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- The original lexicographic pair index, evaluated by exact bounded arithmetic. -/
def generatedAxisGlobalFinitePairIndex (i j : Fin 24) : Fin 276 :=
  let a := min i.val j.val
  let b := max i.val j.val
  ⟨(a * (47 - a) / 2 + b - a - 1) % 276, Nat.mod_lt _ (by decide)⟩

set_option maxHeartbeats 2000000 in
/-- Every distinct physical pair has precisely its original sorted catalogue coordinates. -/
theorem generatedAxisGlobalFinitePairIndex_coordinates (i j : Fin 24) (h : i ≠ j) :
    generatedAxisGlobalPairCoordinates (generatedAxisGlobalFinitePairIndex i j) =
      if i < j then (i, j) else (j, i) := by
  have hc : ∀ i j : Fin 24, i ≠ j →
      generatedAxisGlobalPairCoordinates (generatedAxisGlobalFinitePairIndex i j) =
        if i < j then (i, j) else (j, i) := by decide +kernel
  exact hc i j h

/-- The executable inverse is the entire original intrinsic preferred pair index. -/
theorem generatedAxisGlobalFinitePairIndex_actual (i j : Fin 24) (h : i ≠ j) :
    generatedAxisGlobalFinitePairIndex i j = griessPairIndex i j h := by
  apply griessCoordinatePairEquiv.injective
  apply Subtype.ext
  change griessCoordinatePair (generatedAxisGlobalFinitePairIndex i j) =
    griessCoordinatePair (griessPairIndex i j h)
  rw [← generatedAxisGlobalPairCoordinates_actual,
    generatedAxisGlobalFinitePairIndex_coordinates i j h, griessPairIndex_coordinates]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
