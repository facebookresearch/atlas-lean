/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontChart
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontEvaluationInsertion

/-!
# Whole original mapping-simplex evaluation on the proved right-Hom chart

Every supplied actual right-mapping simplex evaluates the constructed
cube into the same original enriched Hom. The distinguished projection
reads exactly its original whole last-interval map. A constructed Hom
simplex evaluates by the original maximum, and its complete flag recovers
every original scalar cell, without any Kan or weak-comparison premise.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontMappingEvaluation
open SimplicialEnrichment FixedFrontCubeMap FixedFrontInsertion HornHomFaces
variable {C : Carrier.{u}} {n : ℕ} (x y : C)

/-- The actual whole original Hom evaluation of a supplied right-mapping simplex through the proved cube chart. -/
def evaluate
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    RightCubeRelations.object.{u} n ⟶ (x ⟶[SSet.{u}] y) :=
  (FixedFrontCubeIso.cubeIso n).hom ≫ FixedFrontEvaluation.homMap x y σ

/-- Every original distinguished last interval evaluates by the supplied whole enriched mapping simplex with
  the same individual endpoints. -/
theorem interval_evaluate
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋n⦌)
    (i : Fin (n + 1)) :
    intervalMap n i ≫ FixedFrontEvaluation.homMap x y σ =
      retargetMap (RightMappingSimplex.toEnriched x y σ) (.mk (ULift.up i.castSucc))
        (.mk (ULift.up (Fin.last (n + 1)))) (RightMappingSimplex.front_obj x y σ i)
          (RightMappingSimplex.last_obj x y σ) := by
  let a : coherentSimplex.{u} ⦋n + 1⦌ := .mk (ULift.up i.castSucc)
  let b : coherentSimplex.{u} ⦋n + 1⦌ := .mk (ULift.up (Fin.last (n + 1)))
  let F := FixedFrontEvaluation.functor x y σ
  have hr := HomRetargetAlgebra.restriction_reindex (FixedFrontInsertion.functor.{u} n) F a b
    (front_obj n i) (last_obj n) (FixedFrontEvaluation.functor_source x y σ) (FixedFrontEvaluation.functor_target x y σ)
  have he := retargetMap_eq (FixedFrontEvaluationInsertion.insertion x y σ) a b
    ((congrArg F.obj (front_obj n i)).trans (FixedFrontEvaluation.functor_source x y σ))
    ((congrArg F.obj (last_obj n)).trans (FixedFrontEvaluation.functor_target x y σ))
    (RightMappingSimplex.front_obj x y σ i) (RightMappingSimplex.last_obj x y σ)
  exact (Category.assoc ((FixedFrontInsertion.functor n).map a b)
    (eqToHom (congrArg₂ (fun a b : realization (FixedFrontCollapse.object.{u} n) => a ⟶[SSet.{u}] b)
      (front_obj n i) (last_obj n))) (FixedFrontEvaluation.homMap x y σ)).trans (hr.trans he)

/-- The entire original cube projection retains the supplied mapping simplex's whole original zero-to-last Hom map. -/
theorem projection_evaluate
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    RightCubeRelations.projection n ≫ evaluate x y σ =
      retargetMap (RightMappingSimplex.toEnriched x y σ) (.mk (ULift.up (0 : Fin (n + 2))))
        (.mk (ULift.up (Fin.last (n + 1)))) (RightMappingSimplex.front_obj x y σ 0)
          (RightMappingSimplex.last_obj x y σ) :=
  (Category.assoc (RightCubeRelations.projection n) (cubeMap n) (FixedFrontEvaluation.homMap x y σ)).symm.trans
    ((congrArg (fun f => f ≫ FixedFrontEvaluation.homMap x y σ) (cubeMap_projection n)).trans
      (interval_evaluate x y σ 0))

/-- Evaluation of a constructed original Hom simplex is exactly its whole original scalar map after the
  actual quotient maximum. -/
theorem evaluate_constructed (τ : (Δ[n] : SSet.{u}) ⟶ (x ⟶[SSet.{u}] y)) :
    evaluate x y (HomSimplexEndpoints.mappingSimplex x y τ) = RightCubeMaximum.map n ≫ τ := by
  let σ := HomSimplexEndpoints.mappingSimplex x y τ
  have hS : RightMappingSimplex.toEnriched x y σ = HomSimplex.simplex x y τ :=
    (congrArg SSet.yonedaEquiv (HomSimplexEndpoints.mappingSimplex_readback x y τ)).trans
      (SSet.yonedaEquiv.apply_symm_apply _)
  have he := retargetMap_eq hS (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1))))
    (RightMappingSimplex.front_obj x y σ 0) (RightMappingSimplex.last_obj x y σ)
    (HomSimplex.simplex_front x y τ 0) (HomSimplex.simplex_last x y τ)
  have hEval : RightCubeRelations.projection n ≫ evaluate x y σ = HomSimplex.lastMap x y τ 0 :=
    (projection_evaluate x y σ).trans (he.trans (HomSimplex.homMap_last x y τ 0))
  have hMax : RightCubeRelations.projection n ≫ (RightCubeMaximum.map n ≫ τ) = HomSimplex.lastMap x y τ 0 :=
    (Category.assoc (RightCubeRelations.projection n) (RightCubeMaximum.map n) τ).symm.trans
      (congrArg (fun f => f ≫ τ) (RightCubeMaximum.projection_map n))
  ext q a
  induction a using _root_.Quotient.inductionOn with
  | _ a => exact congr($(hEval.trans hMax.symm).app q a)

/-- The actual complete original flag recovers the whole supplied Hom simplex, not a quotient of its objects
  or cells. -/
theorem flag_evaluate_constructed (τ : (Δ[n] : SSet.{u}) ⟶ (x ⟶[SSet.{u}] y)) :
    RightCubeMaximum.sectionMap n ≫ evaluate x y (HomSimplexEndpoints.mappingSimplex x y τ) = τ :=
  (congrArg (fun f => RightCubeMaximum.sectionMap n ≫ f) (evaluate_constructed x y τ)).trans
    ((Category.assoc (RightCubeMaximum.sectionMap n) (RightCubeMaximum.map n) τ).symm.trans
      ((congrArg (fun f => f ≫ τ) (RightCubeMaximum.section_map n)).trans (Category.id_comp τ)))

end CategoryTheory.CoherentRealization.FixedFrontMappingEvaluation
