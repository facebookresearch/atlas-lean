/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingVertices

/-!
# Actual enriched simplices underlying original right mapping spaces

Every supplied simplex of the existing right mapping space is an actual
enriched coherent simplex. Its whole front is the supplied source
identity and its last vertex is the supplied target. All simplex
operators are the actual right-join enriched operators.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightMappingSimplex
open SimplicialEnrichment HomSimplexEndpoints PathMaximumOperators
variable {C : Carrier.{u}} {n m : ℕ} (x y : C)

/-- The actual enriched coherent simplex carried by a supplied original right-mapping simplex. -/
def toEnriched (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) _⦋n⦌) :
    coherentSimplex.{u} ⦋n + 1⦌ ⟶ C := SSet.yonedaEquiv ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n) σ).val

/-- The whole original front of the supplied mapping simplex is the constant enriched simplex at the
  individual source. -/
theorem front (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) _⦋n⦌) :
    coherentSimplexMap (SimplexCategory.δ (Fin.last (n + 1))) ≫ toEnriched x y σ = constantSimplex C ⦋n⦌ x := by
  let t := (SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n) σ
  have hF : SSet.stdSimplex.δ (Fin.last (n + 1)) ≫ t.val = SSet.toDeltaZero (Δ[n] : SSet.{u}) ≫ vertex x :=
    (congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1] => f ≫ t.val) (SSet.frontInclusion_eq n).symm).trans t.2.1
  have hT : SSet.yonedaEquiv (SSet.toDeltaZero (Δ[n] : SSet.{u}) ≫ vertex x) = constantSimplex C ⦋n⦌ x := rfl
  exact (SSet.yonedaEquiv_naturality (SimplexCategory.δ (Fin.last (n + 1))) t.val).trans
    ((congrArg (fun f => SSet.yonedaEquiv f) hF).trans hT)

/-- Every supplied original front vertex retains the same individual original source object. -/
theorem front_obj (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) _⦋n⦌)
    (i : Fin (n + 1)) : (toEnriched x y σ).obj (.mk (ULift.up i.castSucc)) = x := by
  have h := congrArg (fun F : coherentSimplex.{u} ⦋n⦌ ⟶ C => F.obj (.mk (ULift.up i))) (front x y σ)
  have hi : (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom i = i.castSucc := Fin.succAbove_last_apply i
  exact (congrArg (fun j : Fin (n + 2) => (toEnriched x y σ).obj (.mk (ULift.up j))) hi).symm.trans h

/-- The actual last vertex retains the same supplied individual original target object. -/
theorem last_obj (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) _⦋n⦌) :
    (toEnriched x y σ).obj (.mk (ULift.up (Fin.last (n + 1)))) = y := by
  let t := (SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n) σ
  have hF : SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌) ≫ t.val = vertex y :=
    (congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ Δ[n + 1] => f ≫ t.val) (SSet.rightVertex_eq n).symm).trans t.2.2
  have hN : coherentSimplexMap (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌) ≫ toEnriched x y σ = constantSimplex C ⦋0⦌ y :=
    (SSet.yonedaEquiv_naturality (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌) t.val).trans
      ((congrArg (fun f => SSet.yonedaEquiv f) hF).trans (SSet.yonedaEquiv.apply_symm_apply _))
  have h := congrArg (fun F : coherentSimplex.{u} ⦋0⦌ ⟶ C => F.obj zeroPoint) hN
  exact (congrArg (fun j : Fin (n + 2) => (toEnriched x y σ).obj (.mk (ULift.up j)))
    (SSet.inr'_toOrderHom_zero n)).symm.trans h

/-- The original transported simplex follows the actual front operator joined with the last identity. -/
theorem transported_operator (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) _⦋m⦌) :
    ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n)
        ((SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)).map θ.op σ)).val =
      SSet.stdSimplex.map (extension θ) ≫ ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ m) σ).val := by
  let A := (SSet.joinStdSimplexIso.{u} n 0).inv
  let B := (SSet.join.map (SSet.stdSimplex.map θ)).app (Δ[0] : SSet.{u})
  let D := SSet.stdSimplex.map (extension θ)
  let E := (SSet.joinStdSimplexIso.{u} m 0).inv
  have h : A ≫ B = D ≫ E := SSet.joinStdSimplexIso_inv_comp_join_map_app θ 0
  change A ≫ (B ≫ σ.val) = D ≫ (E ≫ σ.val)
  exact (Category.assoc A B _).symm.trans
    ((congrArg (fun f => f ≫ σ.val) h).trans (Category.assoc D E _))

/-- Every actual original enriched mapping simplex follows all faces and degeneracies by right-join precomposition. -/
theorem operator (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) _⦋m⦌) :
    toEnriched x y ((SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)).map θ.op σ) =
      coherentSimplexMap (extension θ) ≫ toEnriched x y σ := by
  exact (congrArg (fun f => SSet.yonedaEquiv f) (transported_operator x y θ σ)).trans
    (SSet.yonedaEquiv_naturality (extension θ) ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ m) σ).val).symm

end CategoryTheory.CoherentRealization.RightMappingSimplex
