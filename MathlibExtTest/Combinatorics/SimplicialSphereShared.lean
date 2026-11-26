/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimplicialSphereShared

open MathlibExt.Combinatorics.SimplicialSphereShared

namespace MathlibExtTest.Combinatorics.SimplicialSphereShared

private noncomputable def emptySphere : FiniteSimplicialSphere 0 where
  K := ⊥
  finite_faces := Set.finite_empty
  sphere_homeomorph := ⟨Homeomorph.setCongr (by
    rw [Geometry.SimplicialComplex.space_bot, Metric.sphere_eq_empty_of_subsingleton one_ne_zero])⟩

-- The empty complex has no ordinary faces and one face of dimension -1.
example (k : ℕ) : faceCount emptySphere k = 0 := by
  simp [faceCount, emptySphere, Geometry.SimplicialComplex.faces_bot]

example : extendedFaceCount emptySphere 0 = 1 ∧ hVector emptySphere 0 = 1 := by
  simp [extendedFaceCount, hVector]

end MathlibExtTest.Combinatorics.SimplicialSphereShared
