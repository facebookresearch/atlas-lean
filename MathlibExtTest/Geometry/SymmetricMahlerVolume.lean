/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Analysis.Convex.HannerPolytope
import MathlibExt.Analysis.InnerProductSpace.CoordinateCubePolar
import MathlibExt.Analysis.InnerProductSpace.PolarSetAdjoint
import MathlibExt.MeasureTheory.Measure.CoordinateCube
import MathlibExt.MeasureTheory.Measure.CoordinateCrossPolytope

open MeasureTheory MetaMathlibExt
open scoped ENNReal

example : IsHannerPolytope hannerUnitSegment := .unitSegment

example : IsHannerPolytope (hannerCube 2) := hannerCube_isHannerPolytope 2

example : IsHannerPolytope (hannerCrossPolytope 1) :=
  hannerCrossPolytope_isHannerPolytope 1

example : Convex ℝ (hannerCube 2) := (hannerCube_isHannerPolytope 2).convex

example : IsCompact (hannerCrossPolytope 1) :=
  (hannerCrossPolytope_isHannerPolytope 1).isCompact

example : (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior (hannerCrossPolytope 1) :=
  (hannerCrossPolytope_isHannerPolytope 1).zero_mem_interior

example : -(hannerCube 2) = hannerCube 2 :=
  (hannerCube_isHannerPolytope 2).neg_eq_self

example : hannerCube 2 = ConvexCovering.coordinateCube 3 :=
  hannerCube_eq_coordinateCube 2

example : volume (ConvexCovering.coordinateCube 1) = 2 := by
  simpa using volume_coordinateCube 1

example : volume (ConvexCovering.coordinateCube 2) = 4 := by
  have h := volume_coordinateCube 2
  norm_num at h ⊢
  exact h

example : volume {x : EuclideanSpace ℝ (Fin 3) | ∑ i, |x i| ≤ 1} = 8 / 6 := by
  have h := volume_coordinateCrossPolytope 3 (by decide)
  norm_num at h ⊢
  exact h

example :
    polarSet (ConvexCovering.coordinateCube 2) =
      {y | ∑ i, |y i| ≤ 1} :=
  polarSet_coordinateCube 2

example : (-2 : ℝ) ∈ polarSet ({1} : Set ℝ) := by
  norm_num [polarSet, inner]

example : ¬ (2 : ℝ) ∈ polarSet ({1} : Set ℝ) := by
  norm_num [polarSet, inner]

example :
    polarSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) =
      Metric.closedBall 0 1 :=
  polarSet_closedUnitBall

example : (0 : EuclideanSpace ℝ (Fin 2)) ∈ polarSet
    {x : EuclideanSpace ℝ (Fin 2) | ∀ i, |x i| ≤ 1} :=
  zero_mem_polarSet _

example : polarSet (∅ : Set (EuclideanSpace ℝ (Fin 2))) = Set.univ :=
  polarSet_empty

example :
    polarSet (((2 : ℝ) • LinearMap.id :
        EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) ''
      {x : EuclideanSpace ℝ (Fin 2) | ∀ i, |x i| ≤ 1}) =
      ((2 : ℝ) • LinearMap.id :
        EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)).adjoint ⁻¹'
        polarSet {x : EuclideanSpace ℝ (Fin 2) | ∀ i, |x i| ≤ 1} :=
  polarSet_image_eq_preimage_adjoint _ _
