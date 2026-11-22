/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeMappingContraction
import MathlibExt.AlgebraicTopology.SimplicialSpace.DiagonalMappingFibrePathFamily
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyMapPrecomp
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyMapPostcomp

/-!
# The whole realized native contraction of an original mapping fibre

The actual path-diagonal map retains the same original mapping parameter.
Its projected native contraction realizes to the complete standard
diagonal edge cylinder, including every point and interval value.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

set_option backward.isDefEq.respectTransparency false in
/-- Realization of the original native contraction on the same mapping fibre is the whole standard edge cylinder. -/
theorem realizedMappingContraction_projection (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    prod.map (𝟙 TopCat.I.{u}) (SSet.toTop.map (mappingToPathDiagonal W x y)) ≫
        SSet.realizeHomotopyMap _ _ (SSet.const (diagonalBasepoint W x))
          (𝟙 (SSet.simplicialDiagonalFunctor.obj (diagram W x))) (nativeDiagonalPointContraction W x) ≫
        SSet.toTop.map (SSet.simplicialDiagonalFunctor.map (projection W x)) =
      realizedMappingFibreCylinder W x y := by
  let H := nativeDiagonalPointContraction W x
  let k := mappingToPathDiagonal W x y
  let p := SSet.simplicialDiagonalFunctor.map (projection W x)
  let H' := (H.precomp k).postcomp p
  have hh : H'.h = (mappingFibreDiagonalHomotopy W x y).h := by
    dsimp only [H', H, k, p]
    rw [SSet.Homotopy.postcomp_h, SSet.Homotopy.precomp_h]
    have hk : mappingToPathDiagonal W x y ▷ (Δ[1] : SSet.{u}) =
        (mappingToPathDiagonal W x y ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) :=
      (MonoidalCategory.tensorHom_id _ _).symm
    rw [hk]
    exact nativeMappingContraction_projection W x y
  rw [← Category.assoc, SSet.realizeHomotopyMap_precomp,
    SSet.realizeHomotopyMap_postcomp]
  exact SSet.realizeHomotopyMap_eq_of_h_eq H' (mappingFibreDiagonalHomotopy W x y) hh

end SimplicialSpace.LeftDecalageObject
