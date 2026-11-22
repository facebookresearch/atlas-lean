/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeRowContraction
import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeContractionMap
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalGroupoidPathFibreReadback

/-!
# The original mapping fibre in the native diagonal contraction

The entire original mapping fibre enters the zero-row path object by its
actual fibre isomorphism. Projecting the native contraction of this same
map is the original diagonal edge cylinder, at every simplex and parameter.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The complete original mapping fibre in the original path diagonal. -/
def mappingToPathDiagonal (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre W x y ⟶ SSet.simplicialDiagonalFunctor.obj (diagram W x) :=
  (zeroMappingFibreIso W x y).hom ≫
    pullback.fst ((projection W x).app (op (SimplexCategory.mk 0))) (SSet.yonedaEquiv.symm y) ≫
    pathZeroToDiagonal W x

set_option backward.isDefEq.respectTransparency false in
/-- The projected native contraction of the same whole mapping parameter is the actual edge interval. -/
theorem nativeMappingContraction_projection (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (mappingToPathDiagonal W x y ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫
        (nativeDiagonalPointContraction W x).h ≫ SSet.simplicialDiagonalFunctor.map (projection W x) =
      mappingFibreDiagonalCylinder W x y := by
  let a : mappingFibre W x y ⟶ (diagram W x).obj (op (SimplexCategory.mk 0)) :=
    (zeroMappingFibreIso W x y).hom ≫
      pullback.fst ((projection W x).app (op (SimplexCategory.mk 0))) (SSet.yonedaEquiv.symm y)
  have ha : a ≫ (toDecalage W x).app (op (SimplexCategory.mk 0)) = mappingFibre.fst W x y :=
    zeroMappingFibreIso_edge W x y
  change ((a ≫ pathZeroToDiagonal W x) ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫ _ ≫ _ = _
  rw [nativeDiagonalPointContraction_h]
  have ht : ((a ≫ pathZeroToDiagonal W x) ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) =
      (a ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫ (pathZeroToDiagonal W x ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  rw [ht, Category.assoc, nativeRowZeroContraction_projection]
  have he : (a ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫
      ((toDecalage W x).app (op (SimplexCategory.mk 0)) ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) =
      (mappingFibre.fst W x y ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp, ha]
  rw [← Category.assoc, he]
  rfl

end SimplicialSpace.LeftDecalageObject
