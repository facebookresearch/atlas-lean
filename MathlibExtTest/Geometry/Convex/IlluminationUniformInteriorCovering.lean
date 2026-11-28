/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Convex.CubeCovering
import MathlibExt.Geometry.Convex.IlluminationUniformInteriorCovering

/-! # Tests for uniform directional illumination -/

open ConvexCovering Set

-- A uniform bound gives illumination of the one-dimensional cube by the same number.
example (h : UniformInteriorTranslateBound 1 2) : IlluminatedByDirections (coordinateCube 1) 2 :=
  (uniformDirectionalIlluminationInterpretation 1 (by decide) 2).mp h
    (coordinateCube 1) (coordinateCube_isConvexBody 1)

-- Zero directions cannot give a uniform bound, since the cube cannot be covered by zero sets.
example : ¬ (∀ K : Set (EuclideanSpace ℝ (Fin 1)), IsConvexBody K → IlluminatedByDirections K 0) := by
  intro h
  have hK := coordinateCube_isConvexBody 1
  have hCover := (uniformDirectionalIlluminationInterpretation 1 (by decide) 0).mpr h _ hK
  obtain ⟨_, hTranslations⟩ := (coveredByTranslates_iff _ _).mp hCover
  obtain ⟨x, hx⟩ := hK.2.2.mono interior_subset
  obtain ⟨i, _⟩ := hTranslations x hx
  exact Fin.elim0 i
