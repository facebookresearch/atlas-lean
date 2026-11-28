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

private lemma unitSphere_ncard : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1).ncard = 2 := by
  let e := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  have hs := e.toIsometryEquiv.image_sphere 0 1
  change e '' Metric.sphere 0 1 = Metric.sphere (e 0) 1 at hs
  rw [e.map_zero] at hs
  rw [← hs, Set.ncard_image_of_injective _ e.injective, Real.sphere_eq_pair _ zero_le_one,
    Set.ncard_pair]
  norm_num

-- The zero-sphere consists of the endpoints of [-1, 1], each a singleton face.
private noncomputable def twoPointSphere : FiniteSimplicialSphere 1 where
  K := {
    faces := (fun x ↦ {x}) '' Metric.sphere 0 1
    isRelLowerSet_faces := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨Finset.singleton_nonempty x, fun t hsub ht ↦ ?_⟩
      exact ⟨x, hx, (ht.subset_singleton_iff.mp hsub).symm⟩
    indep := by
      rintro _ ⟨x, _, rfl⟩
      exact affineIndependent_of_subsingleton _ _
    inter_subset_convexHull := by
      rintro _ _ ⟨x, _, rfl⟩ ⟨y, _, rfl⟩
      simpa only [Finset.coe_singleton, convexHull_singleton] using
        subset_convexHull ℝ (({x} : Set _) ∩ {y}) }
  finite_faces := (Set.finite_of_ncard_pos (by rw [unitSphere_ncard]; decide)).image _
  sphere_homeomorph := ⟨Homeomorph.setCongr (by
    ext x
    simp [Geometry.SimplicialComplex.space])⟩

private lemma twoPointSphere_faceCount_zero : faceCount twoPointSphere 0 = 2 := by
  unfold faceCount
  rw [Set.sep_eq_self_iff_mem_true.mpr ?_]
  · exact (Set.ncard_image_of_injective _ Finset.singleton_injective).trans unitSphere_ncard
  · rintro _ ⟨x, _, rfl⟩
    simp

example : faceCount twoPointSphere 1 = 0 := by
  rw [faceCount, Set.sep_eq_empty_iff_mem_false.mpr ?_, Set.ncard_empty]
  rintro _ ⟨x, _, rfl⟩
  simp

example : hVector twoPointSphere 1 = 1 := by
  simp [hVector, Finset.sum_range_succ, extendedFaceCount, twoPointSphere_faceCount_zero]

end MathlibExtTest.Combinatorics.SimplicialSphereShared
