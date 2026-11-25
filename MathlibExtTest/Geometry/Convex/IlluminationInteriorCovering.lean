/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Convex.CubeCovering
import MathlibExt.Geometry.Convex.IlluminationInteriorCovering

open ConvexCovering Set

-- The three-dimensional cube needs eight directions, just as it needs eight translates.
example : directionalIlluminationNumber (coordinateCube 3) = (8 : WithTop ℕ) := by
  rw [directionalInteriorCoveringNumbersEqual 3 (by decide) _ (coordinateCube_isConvexBody 3)]
  exact coordinateCube_three_translateCoveringNumber

local notation "K₀" => (univ : Set (EuclideanSpace ℝ (Fin 0)))

-- In dimension zero the whole space has empty boundary, but a cover still needs one translate.
example : directionalIlluminationNumber K₀ = 0 ∧ translateCoveringNumber K₀ (interior K₀) = 1 := by
  rw [interior_univ]
  constructor
  · have h : IsLeast {q : ℕ | IlluminatedByDirections K₀ q} 0 :=
      ⟨⟨Fin.elim0, fun i ↦ i.elim0, by simp⟩, fun _ _ ↦ Nat.zero_le _⟩
    exact (WithTop.coe_mono.map_isLeast h).csInf_eq
  · apply translateCoveringNumber_eq_of_isLeast _ _ (q := 1)
    constructor
    · exact (coveredByTranslates_iff _ _).mpr
        ⟨fun _ ↦ 0, fun x _ ↦ ⟨0, x, mem_univ x, zero_add x⟩⟩
    · intro q hq
      obtain ⟨w, hw⟩ := (coveredByTranslates_iff _ _).mp hq
      obtain ⟨i, _⟩ := hw 0 (mem_univ _)
      exact Nat.zero_lt_of_lt i.isLt
