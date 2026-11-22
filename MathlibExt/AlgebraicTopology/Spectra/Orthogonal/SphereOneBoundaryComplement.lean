/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.IntervalOnePointSphere
public import MathlibExt.Topology.Category.PointedCGWH.SphereOne
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Boundary
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizationBoundaryZeroCoordinate

/-!
# The exact original one-sphere boundary complement

The original `sphereOne` collapses the realized boundary of the one-simplex.
The entire realized boundary is exactly the two interval endpoints, and its
complement is the lifted Euclidean line. All closedness and endpoint claims
are derived from the original realization and its actual coordinate maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Set Topology
open scoped Simplicial

namespace CategoryTheory.Spectra

/-- The original CGWH boundary arrow used in `sphereOne`. -/
def sphereOneBoundaryArrow : Arrow CGWH.{u, v} :=
  Arrow.mk (SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι)

/-- The original one-simplex realization is the literal native interval. -/
def sphereOneIntervalHomeomorph :
    sphereOneBoundaryArrow.{u, v}.right ≃ₜ TopCat.I.{v} :=
  TopCat.homeoOfIso
    (SSet.realizationToTopIso.{u, v}.app (Δ[1] : SSet.{v}) ≪≫
      SSet.stdSimplex.toTopObjIsoI)

/-- The original realized boundary embeds closedly in the original realized interval. -/
theorem sphereOneBoundaryArrow_closedEmbedding :
    IsClosedEmbedding (ConcreteCategory.hom sphereOneBoundaryArrow.{u, v}.hom) := by
  change IsClosedEmbedding (SSet.toTop.{v}.map (SSet.boundary.{v} 1).ι)
  exact TopCat.closedT1Embeddings_le_isClosedEmbedding _
    (SSet.boundary.closedT1Embeddings_toTop_map_ι 1)

/-- A realized point is in the original boundary precisely at an interval endpoint. -/
theorem sphereOneBoundaryArrow_mem_range (x : sphereOneBoundaryArrow.{u, v}.right) :
    x ∈ Set.range sphereOneBoundaryArrow.{u, v}.hom ↔
      sphereOneIntervalHomeomorph.{u, v} x = 0 ∨
        sphereOneIntervalHomeomorph.{u, v} x = 1 := by
  let p : Convexity.StdSimplex ℝ (Fin 2) := (SimplexCategory.toTopHomeo ⦋1⦌) x
  have hsum : p.weights 0 + p.weights 1 = 1 := by
    simpa only [Fin.sum_univ_two] using p.total_of_fintype
  have hcoord : (TopCat.I.homeomorph (sphereOneIntervalHomeomorph.{u, v} x)).val =
      p.weights 1 := by
    exact Convexity.StdSimplex.homeomorphI_apply_coe p
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := SSet.boundary.mem_zeroCoord_of_mem_realizedBoundaryRange 1 x hx
    fin_cases j
    · right
      change p.weights 0 = 0 at hj
      apply TopCat.I.homeomorph.injective
      apply Subtype.ext
      change (TopCat.I.homeomorph (sphereOneIntervalHomeomorph.{u, v} x)).val = 1
      rw [hcoord]
      linarith
    · left
      change p.weights 1 = 0 at hj
      apply TopCat.I.homeomorph.injective
      apply Subtype.ext
      rw [hcoord]
      exact hj
  · intro hx
    have hmem : (SimplexCategory.toTopHomeo ⦋1⦌).symm p ∈
        Set.range (SSet.toTop.{v}.map (SSet.boundary.{v} 1).ι) := by
      rcases hx with hx | hx
      · apply SSet.mem_realizedBoundary_of_zeroCoord 1 p 1
        rw [← hcoord, hx]
        rfl
      · apply SSet.mem_realizedBoundary_of_zeroCoord 1 p 0
        have h1 : p.weights 1 = 1 := by
          rw [← hcoord, hx]
          rfl
        linarith
    change x ∈ Set.range (SSet.toTop.{v}.map (SSet.boundary.{v} 1).ι)
    have hp : (SimplexCategory.toTopHomeo ⦋1⦌).symm p = x :=
      (SimplexCategory.toTopHomeo ⦋1⦌).symm_apply_apply x
    rw [hp] at hmem
    exact hmem

/-- The entire original boundary range maps to exactly the two ordered interval endpoints. -/
theorem sphereOneBoundaryArrow_range :
    sphereOneIntervalHomeomorph.{u, v} '' Set.range sphereOneBoundaryArrow.{u, v}.hom =
      {(0 : TopCat.I.{v}), 1} := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (sphereOneBoundaryArrow_mem_range x).mp hx
  · intro ht
    refine ⟨sphereOneIntervalHomeomorph.{u, v}.symm t, ?_,
      sphereOneIntervalHomeomorph.{u, v}.apply_symm_apply t⟩
    rw [sphereOneBoundaryArrow_mem_range, Homeomorph.apply_symm_apply]
    exact ht

/-- The complement of the original realized boundary is the actual lifted Euclidean line. -/
def sphereOneBoundaryComplement : ULift.{v, 0} (EuclideanSpace ℝ (Fin 1)) ≃ₜ
    ((Set.range sphereOneBoundaryArrow.{u, v}.hom)ᶜ :
      Set sphereOneBoundaryArrow.{u, v}.right) := by
  let e := sphereOneIntervalHomeomorph.{u, v}
  let r := e.image ((Set.range sphereOneBoundaryArrow.{u, v}.hom)ᶜ : Set _)
  have hr : e '' ((Set.range sphereOneBoundaryArrow.{u, v}.hom)ᶜ : Set _) =
      ({(0 : TopCat.I.{v}), 1}ᶜ : Set TopCat.I.{v}) := by
    rw [e.image_compl, sphereOneBoundaryArrow_range]
  exact liftedEuclideanIntervalComplement.trans
    ((Homeomorph.setCongr hr).symm.trans r.symm)

end CategoryTheory.Spectra
