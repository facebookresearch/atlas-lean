/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRawRightMappingRealization
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornMapNaturality

/-!
# SAME original raw mapping comparison source naturality

Every original source simplicial map preserves the complete
fixed-front quotient evaluation, both exact original endpoints
and the entire realized Hom comparison. No Kan or weak-comparison
outcome is a hypothesis.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping
open SimplicialEnrichment FixedFrontCollapse
variable {K L : SSet.{u}} {n : ℕ}
  (a b : (Δ[0] : SSet.{u}) ⟶ K) (F : K ⟶ L)

/-- The SAME full original right-mapping successor simplex is postcomposed by its original source map. -/
theorem successor_map (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    successor (a ≫ F) (b ≫ F) ((SSet.mappingSpaceRight.map K a b F).app (op ⦋n⦌) σ) =
      successor a b σ ≫ F := (Category.assoc _ _ _).symm

/-- The complete original quotient evaluation follows the SAME original source simplicial map. -/
theorem quotientMap_map (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    quotientMap a b σ ≫ F =
      quotientMap (a ≫ F) (b ≫ F) ((SSet.mappingSpaceRight.map K a b F).app (op ⦋n⦌) σ) := by
  have h : projection n ≫ (quotientMap a b σ ≫ F) =
      projection n ≫ quotientMap (a ≫ F) (b ≫ F)
        ((SSet.mappingSpaceRight.map K a b F).app (op ⦋n⦌) σ) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ F) (quotientMap_projection a b σ)).trans
        ((successor_map a b F σ).symm.trans (quotientMap_projection (a ≫ F) (b ≫ F) _).symm))
  ext q x
  induction x using _root_.Quotient.inductionOn with
  | _ x => exact congr($(h).app q x)

/-- The entire SAME original raw enriched evaluation follows the actual original source map. -/
theorem evaluation_map (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    evaluation a b σ ≫ realizationMap F =
      evaluation (a ≫ F) (b ≫ F) ((SSet.mappingSpaceRight.map K a b F).app (op ⦋n⦌) σ) :=
  (realizationMap_comp _ _).symm.trans
    (congrArg realizationMap (quotientMap_map a b F σ))

/-- The exact original endpoint equation for a supplied vertex map and its SAME whole source simplicial map. -/
theorem vertex_map (a : (Δ[0] : SSet.{u}) ⟶ K) :
    (realizationMap F).obj (SSet.yonedaEquiv a) = SSet.yonedaEquiv (a ≫ F) :=
  (SSet.yonedaEquiv_comp a F).symm

/-- The SAME full original raw realization Hom map with precisely the original two vertex-image equations. -/
def targetHomMap :
    hom K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b) ⟶
      hom L (SSet.yonedaEquiv (a ≫ F)) (SSet.yonedaEquiv (b ≫ F)) :=
  (realizationMap F).map (SSet.yonedaEquiv a) (SSet.yonedaEquiv b) ≫
    eqToHom (congrArg₂ (hom L) (vertex_map F a) (vertex_map F b))

/-- Every SAME full original fixed-front Hom coefficient retains its complete source naturality square. -/
theorem homEvaluation_map (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    homEvaluation a b σ ≫ targetHomMap a b F =
      homEvaluation (a ≫ F) (b ≫ F) ((SSet.mappingSpaceRight.map K a b F).app (op ⦋n⦌) σ) := by
  let G := evaluation a b σ
  let R := realizationMap F
  let σ' := (SSet.mappingSpaceRight.map K a b F).app (op ⦋n⦌) σ
  have hPost := HornMapNaturality.retargetMap_postcompose G R (source n) (target n)
    (evaluation_source a b σ) (evaluation_target a b σ)
  have hTrans := HomRetargetAlgebra.target_trans (G ≫ R) (source n) (target n)
    (congrArg R.obj (evaluation_source a b σ)) (congrArg R.obj (evaluation_target a b σ))
    (vertex_map F a) (vertex_map F b)
  have hEq := HornHomFaces.retargetMap_eq (evaluation_map a b F σ) (source n) (target n)
    ((congrArg R.obj (evaluation_source a b σ)).trans (vertex_map F a))
    ((congrArg R.obj (evaluation_target a b σ)).trans (vertex_map F b))
    (evaluation_source (a ≫ F) (b ≫ F) σ') (evaluation_target (a ≫ F) (b ≫ F) σ')
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ eqToHom (congrArg₂ (hom L) (vertex_map F a) (vertex_map F b)))
      hPost).trans (hTrans.trans hEq))

/-- Every SAME whole original quotient-cube coefficient preserves the complete original source naturality square. -/
theorem cubeEvaluation_map (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    cubeEvaluation a b σ ≫ targetHomMap a b F =
      cubeEvaluation (a ≫ F) (b ≫ F) ((SSet.mappingSpaceRight.map K a b F).app (op ⦋n⦌) σ) :=
  (Category.assoc _ _ _).trans
    (congrArg (fun q => (FixedFrontCubeIso.cubeIso n).hom ≫ q) (homEvaluation_map a b F σ))

/-- The SAME entire original raw right-mapping realization comparison is natural for every original source simplicial
map. -/
theorem realizationComparison_map :
    OriginalRightCubeRealization.map (SSet.mappingSpaceRight.map K a b F) ≫
      realizationComparison (a ≫ F) (b ≫ F) =
    realizationComparison a b ≫ targetHomMap a b F := by
  apply colimit.hom_ext
  intro e
  have hMap := OriginalRightCubeRealization.insertion_map (SSet.mappingSpaceRight.map K a b F) e
  have hL := colimit.ι_desc (evaluationCocone (a ≫ F) (b ≫ F))
    ((SSet.mappingSpaceRight.map K a b F).mapElements.op.obj e)
  have hR := colimit.ι_desc (evaluationCocone a b) e
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ realizationComparison (a ≫ F) (b ≫ F)) hMap).trans
      (hL.trans
        ((cubeEvaluation_map a b F e.unop.val).symm.trans
          ((congrArg (fun q => q ≫ targetHomMap a b F) hR.symm).trans (Category.assoc _ _ _)))))

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
