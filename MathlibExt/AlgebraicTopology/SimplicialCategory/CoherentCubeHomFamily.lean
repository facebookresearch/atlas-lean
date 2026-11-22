/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeFrontFamily
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFrontFamilyEndpoints
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontMappingEvaluation

/-!
# Actual original right-mapping simplices from whole cube Hom maps

Every supplied whole cube-to-Hom map gives the genuine front-compatible
last-interval family and an actual enriched successor simplex. Its
original individual source and target are retained. Evaluation recovers
the whole supplied original map in every scalar degree, without a Kan
or mapping-weak outcome hypothesis.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.CubeHomFamily
open SimplicialEnrichment HornHomFaces
variable {C : Carrier.{u}} {n : ℕ} (x y : C)

/-- The actual original last-interval family carried by a supplied whole cube Hom map. -/
def family (f : RightCubeRelations.object.{u} n ⟶ (x ⟶[SSet.{u}] y)) : HomFrontFamily.Family x y n where
  map i := nerveMap (RightCubeRelations.prependFunctor i) ≫ RightCubeRelations.projection n ≫ f
  map_comp i j q p r := congrArg (f.app q) (RightCubeFrontFamily.quotient_union i j q p r)

/-- The actual original right-mapping simplex constructed from that same whole cube Hom map and individual endpoints. -/
def construct (f : RightCubeRelations.object.{u} n ⟶ (x ⟶[SSet.{u}] y)) :
    (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋n⦌ :=
  HomFrontFamilyEndpoints.mappingSimplex x y (family x y f)

/-- Its whole original enriched simplex is precisely the constructed original last-interval family. -/
theorem enriched_construct (f : RightCubeRelations.object.{u} n ⟶ (x ⟶[SSet.{u}] y)) :
    RightMappingSimplex.toEnriched x y (construct x y f) = HomFrontFamily.simplex x y (family x y f) :=
  (congrArg (fun a : (Δ[n + 1] : SSet.{u}) ⟶ coherentNerveFunctor.obj C => SSet.yonedaEquiv a)
    (HomFrontFamilyEndpoints.mappingSimplex_readback x y (family x y f))).trans
      ((SSet.yonedaEquiv (X := coherentNerveFunctor.obj C) (n := ⦋n + 1⦌)).apply_symm_apply _)

/-- The whole actual original cube Hom map is exactly recovered by evaluation of its constructed original
  right-mapping simplex. -/
theorem evaluate_construct (f : RightCubeRelations.object.{u} n ⟶ (x ⟶[SSet.{u}] y)) :
    FixedFrontMappingEvaluation.evaluate x y (construct x y f) = f := by
  let σ := construct x y f
  have he := retargetMap_eq (enriched_construct x y f)
    (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1))))
    (RightMappingSimplex.front_obj x y σ 0) (RightMappingSimplex.last_obj x y σ)
    (HomFrontFamily.simplex_front x y (family x y f) 0) (HomFrontFamily.simplex_last x y (family x y f))
  have h0 : RightCubeRelations.projection n ≫ FixedFrontMappingEvaluation.evaluate x y σ = (family x y f).map 0 :=
    (FixedFrontMappingEvaluation.projection_evaluate x y σ).trans
      (he.trans (HomFrontFamily.homMap_last x y (family x y f) 0))
  have hN : nerveMap (RightCubeRelations.prependFunctor.{u} (0 : Fin (n + 1))) = 𝟙 _ := by
    rw [FixedFrontCubeRetraction.prepend_zero]
    rfl
  have hF : (family x y f).map 0 = RightCubeRelations.projection n ≫ f := by
    change nerveMap (RightCubeRelations.prependFunctor (0 : Fin (n + 1))) ≫ RightCubeRelations.projection n ≫ f = _
    rw [hN, Category.id_comp]
  ext q a
  induction a using _root_.Quotient.inductionOn with
  | _ p => exact congr($(h0.trans hF).app q p)

end CategoryTheory.CoherentRealization.CubeHomFamily
