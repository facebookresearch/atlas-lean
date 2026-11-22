/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontPointedReadbacks
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRawRightMappingEvaluation
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontProjectionEpi

/-!
# The SAME original right-mapping space is the pointed resolution Hom space

Every complete original right-mapping simplex factors through the SAME
fixed-front quotient with both original endpoints. Conversely every map
from that endpoint-fixed quotient reads the complete original successor
simplex, front and last vertex. Both inverse maps retain the original
quotient maps, all scalar operators and every input source map.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

open OriginalFixedFrontContraction

variable {K : SSet.{u}} (a b : (Δ[0] : SSet.{u}) ⟶ K)

/-- The SAME original input with its literal two original endpoint boundary maps. -/
def pointedInput : Under (∂Δ[1] : SSet.{u}) :=
  Under.mk (SSet.boundaryOneMap (SSet.yonedaEquiv a) (SSet.yonedaEquiv b))

/-- Every original right-mapping simplex retains its SAME entire quotient map as a pointed morphism. -/
def toPointedMap {n : ℕ} (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) : pointedObject.{u} n ⟶ pointedInput a b :=
  Under.homMk (quotientMap a b σ)
    ((SSet.boundaryOneMap_naturality (quotientMap a b σ) (FixedFrontCollapse.source n)
      (FixedFrontCollapse.target n)).trans
        (congrArg₂ SSet.boundaryOneMap (evaluation_source a b σ) (evaluation_target a b σ)))

private theorem toDeltaZero_comp_const (n : ℕ) (a : (Δ[0] : SSet.{u}) ⟶ K) :
    SSet.toDeltaZero (Δ[n] : SSet.{u}) ≫ a = SSet.const (SSet.yonedaEquiv a) := by
  let v : (Δ[0] : SSet.{u}) _⦋0⦌ := SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))
  have h := SSet.toDeltaZero_eq (SSet.const (X := (Δ[n] : SSet.{u})) v)
  have hv : a.app (op ⦋0⦌) v = SSet.yonedaEquiv a :=
    (SSet.yonedaEquiv_comp (𝟙 (Δ[0] : SSet.{u})) a).symm.trans
      (congrArg SSet.yonedaEquiv (Category.id_comp a))
  exact (congrArg (fun f => f ≫ a) h.symm).trans
    ((SSet.const_comp v a).trans (congrArg SSet.const hv))

private theorem rightVertex_projection_const (n : ℕ) :
    SSet.rightVertex n ≫ FixedFrontCollapse.projection.{u} n = SSet.const (FixedFrontCollapse.target n) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_const, SSet.yonedaEquiv_comp, SSet.rightVertex_eq, SSet.yonedaEquiv_map]
  apply congrArg ((FixedFrontCollapse.projection n).app (op ⦋0⦌))
  apply SSet.stdSimplex.objEquiv.injective
  simp only [Equiv.apply_symm_apply]
  ext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact congrArg Fin.val (SSet.inr'_toOrderHom_zero n)

/-- Every SAME entire pointed quotient map has its literal original successor simplex and full endpoint equations. -/
def fromPointedMap {n : ℕ} (g : pointedObject.{u} n ⟶ pointedInput a b) :
    (SSet.mappingSpaceRight K a b) _⦋n⦌ :=
  (SSet.mappingSpaceRight.simplexEquivSucc K a b n).symm
    ⟨FixedFrontCollapse.projection n ≫ g.right, by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ g.right) (projection_front_const n)).trans
          ((SSet.const_comp (FixedFrontCollapse.source n) g.right).trans
            ((congrArg SSet.const (pointedHom_vertices (SSet.yonedaEquiv a) (SSet.yonedaEquiv b) g).1).trans
              (toDeltaZero_comp_const n a).symm))), by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ g.right) (rightVertex_projection_const n)).trans
          ((SSet.const_comp (FixedFrontCollapse.target n) g.right).trans
            ((congrArg SSet.const (pointedHom_vertices (SSet.yonedaEquiv a) (SSet.yonedaEquiv b) g).2).trans
              ((SSet.yonedaEquiv_symm_zero (SSet.yonedaEquiv b)).symm.trans
                (Equiv.symm_apply_apply SSet.yonedaEquiv b)))))⟩

/-- Both original quotient directions give the SAME right-mapping simplex after the pointed roundtrip. -/
theorem fromPointedMap_toPointedMap {n : ℕ} (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    fromPointedMap a b (toPointedMap a b σ) = σ := by
  apply (SSet.mappingSpaceRight.simplexEquivSucc K a b n).injective
  apply Subtype.ext
  dsimp only [fromPointedMap]
  rw [Equiv.apply_symm_apply]
  exact quotientMap_projection a b σ

/-- The original pointed-to-right-mapping direction retains its SAME full projected successor map. -/
theorem fromPointedMap_successor {n : ℕ} (g : pointedObject.{u} n ⟶ pointedInput a b) :
    successor a b (fromPointedMap a b g) = FixedFrontCollapse.projection n ≫ g.right := by
  exact congrArg Subtype.val
    ((SSet.mappingSpaceRight.simplexEquivSucc K a b n).apply_symm_apply _)

/-- Both original quotient directions give the SAME entire pointed map after the right-mapping roundtrip. -/
theorem toPointedMap_fromPointedMap {n : ℕ} (g : pointedObject.{u} n ⟶ pointedInput a b) :
    toPointedMap a b (fromPointedMap a b g) = g := by
  apply Under.UnderMorphism.ext
  let _ := projection_epi.{u} n
  apply (cancel_epi (FixedFrontCollapse.projection.{u} n)).1
  exact (quotientMap_projection a b (fromPointedMap a b g)).trans (fromPointedMap_successor a b g)

/-- Every original right-mapping scalar has the SAME full pointed-quotient Hom equivalence. -/
def pointedHomEquiv (n : ℕ) : (SSet.mappingSpaceRight K a b) _⦋n⦌ ≃ (pointedObject.{u} n ⟶ pointedInput a b) where
  toFun := toPointedMap a b
  invFun := fromPointedMap a b
  left_inv := fromPointedMap_toPointedMap a b
  right_inv := toPointedMap_fromPointedMap a b

/-- The original right-mapping-to-pointed direction is literally its SAME entire original quotient map. -/
theorem pointedHomEquiv_right (n : ℕ) (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    ((pointedHomEquiv a b n) σ).right = quotientMap a b σ := rfl

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
