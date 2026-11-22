/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontUniversalMap
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontChart
import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSlice

/-!
# Actual fixed-front evaluation into the SAME original realization

Every full original right-mapping simplex of an arbitrary simplicial
set factors through the original fixed-front quotient. Its original
coherent realization evaluates every whole coefficient into the
SAME raw realization Hom at its original endpoints.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping
open SimplicialEnrichment FixedFrontCollapse

variable {K : SSet.{u}} {n m : ℕ}
  (a b : (Δ[0] : SSet.{u}) ⟶ K)

/-- The entire original right-mapping successor simplex under the existing transported join isomorphism. -/
def successor (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) : (Δ[n+1] : SSet.{u}) ⟶ K :=
  ((SSet.mappingSpaceRight.simplexEquivSucc K a b n) σ).val

/-- The SAME successor simplex factors through the actual complete original fixed-front quotient. -/
def quotientMap (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    FixedFrontCollapse.object.{u} n ⟶ K :=
  FixedFrontUniversalMap.lift (successor a b σ) a
    ((SSet.mappingSpaceRight.simplexEquivSucc K a b n) σ).property.1

/-- The whole original quotient map retains the entire original supplied successor prism. -/
theorem quotientMap_projection (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    projection n ≫ quotientMap a b σ = successor a b σ :=
  FixedFrontUniversalMap.projection_lift _ _ _

/-- The SAME original successor simplex follows every actual right-join face and degeneracy. -/
theorem successor_operator (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (σ : (SSet.mappingSpaceRight K a b) _⦋m⦌) :
    successor a b ((SSet.mappingSpaceRight K a b).map θ.op σ) =
      SSet.stdSimplex.map (PathMaximumOperators.extension θ) ≫ successor a b σ := by
  let A := (SSet.joinStdSimplexIso.{u} n 0).inv
  let B := (SSet.join.map (SSet.stdSimplex.map θ)).app (Δ[0] : SSet.{u})
  let D := SSet.stdSimplex.map (PathMaximumOperators.extension θ)
  let E := (SSet.joinStdSimplexIso.{u} m 0).inv
  have h : A ≫ B = D ≫ E := SSet.joinStdSimplexIso_inv_comp_join_map_app θ 0
  change A ≫ (B ≫ σ.val) = D ≫ (E ≫ σ.val)
  exact (Category.assoc A B _).symm.trans
    ((congrArg (fun q => q ≫ σ.val) h).trans (Category.assoc D E _))

/-- The entire SAME raw quotient evaluation is natural for all original right-mapping operators. -/
theorem quotientMap_operator (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (σ : (SSet.mappingSpaceRight K a b) _⦋m⦌) :
    FixedFrontOperators.map θ ≫ quotientMap a b σ =
      quotientMap a b ((SSet.mappingSpaceRight K a b).map θ.op σ) := by
  have h : projection n ≫ (FixedFrontOperators.map θ ≫ quotientMap a b σ) =
      projection n ≫ quotientMap a b ((SSet.mappingSpaceRight K a b).map θ.op σ) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ quotientMap a b σ) (FixedFrontOperators.projection_map θ)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun q => SSet.stdSimplex.map (PathMaximumOperators.extension θ) ≫ q)
            (quotientMap_projection a b σ)).trans
              ((successor_operator a b θ σ).symm.trans
                (quotientMap_projection a b _).symm))))
  ext q x
  induction x using _root_.Quotient.inductionOn with
  | _ x => exact congr($(h).app q x)

/-- The SAME whole original raw coherent realization evaluation of each supplied mapping simplex. -/
def evaluation (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    realization (FixedFrontCollapse.object.{u} n) ⟶ realization K :=
  realizationFunctor.map (quotientMap a b σ)

/-- The original raw evaluation retains exactly its whole original realization map. -/
theorem evaluation_original (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    evaluation a b σ = realizationMap (quotientMap a b σ) := rfl

/-- Every SAME original full enriched evaluation square follows the actual right-mapping ordinal operator. -/
theorem evaluation_operator (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (σ : (SSet.mappingSpaceRight K a b) _⦋m⦌) :
    realizationMap (FixedFrontOperators.map θ) ≫ evaluation a b σ =
      evaluation a b ((SSet.mappingSpaceRight K a b).map θ.op σ) :=
  (realizationMap_comp _ _).symm.trans
    (congrArg realizationMap (quotientMap_operator a b θ σ))

/-- The SAME original source quotient vertex evaluates to the original supplied source vertex. -/
theorem evaluation_source (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    (evaluation a b σ).obj (source n) = SSet.yonedaEquiv a := by
  let t := (SSet.mappingSpaceRight.simplexEquivSucc K a b n) σ
  let z := SSet.stdSimplex.objEquiv.{u}.symm (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)
  have hProj : (SSet.frontInclusion n).app (op ⦋0⦌) z =
      SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋n+1⦌ 0) := by
    rw [SSet.frontInclusion_eq]
    apply SSet.stdSimplex.objEquiv.injective
    ext i : 3
    rfl
  have hFront := congrArg (fun q => q.app (op ⦋0⦌) z) t.property.1
  change t.val.app (op ⦋0⦌) ((SSet.frontInclusion n).app (op ⦋0⦌) z) =
    a.app (op ⦋0⦌) ((SSet.toDeltaZero (Δ[n] : SSet.{u})).app (op ⦋0⦌) z) at hFront
  rw [hProj] at hFront
  have hZero : ((SSet.toDeltaZero (Δ[n] : SSet.{u})).app (op ⦋0⦌) z) =
      SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌) := by
    apply SSet.stdSimplex.objEquiv.injective
    ext i : 3
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  rw [hZero] at hFront
  exact hFront

/-- The SAME original target quotient vertex evaluates to the original supplied last vertex. -/
theorem evaluation_target (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    (evaluation a b σ).obj (target n) = SSet.yonedaEquiv b := by
  let t := (SSet.mappingSpaceRight.simplexEquivSucc K a b n) σ
  have hLast : SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌) ≫ t.val = b :=
    (congrArg (fun q => q ≫ t.val) (SSet.rightVertex_eq n).symm).trans t.property.2
  have h := congrArg (fun q => q.app (op ⦋0⦌)
    (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))) hLast
  have hVertex : (SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌)).app (op ⦋0⦌)
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) =
    SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋n+1⦌ (Fin.last (n+1))) := by
    apply SSet.stdSimplex.objEquiv.injective
    ext i : 3
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact SSet.inr'_toOrderHom_zero n
  change t.val.app (op ⦋0⦌) ((SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌)).app (op ⦋0⦌)
    (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))) = _ at h
  rw [hVertex] at h
  exact h

/-- The complete SAME original raw Hom evaluation with precisely its two supplied original vertex equations. -/
def homEvaluation (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    FixedFrontCollapse.rightHom.{u} n ⟶ CoherentRealization.hom K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b) :=
  (evaluation a b σ).map (source n) (target n) ≫
    eqToHom (congrArg₂ (CoherentRealization.hom K) (evaluation_source a b σ) (evaluation_target a b σ))

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
